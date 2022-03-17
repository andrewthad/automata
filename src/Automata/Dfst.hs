{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language UnboxedTuples #-}

module Automata.Dfst
  ( -- * Static
    -- ** Types
    Dfst
    -- ** Functions
  , evaluate
  , evaluateAscii
  , union
  , boundedUnion
  , map
    -- ** Properties
  , states
  , transitions
    -- ** Special Transducers
  , rejection
    -- * Builder
    -- ** Types
  , Builder
  , State
    -- ** Functions
  , build
  , buildDefaulted
  , state
  , transition
  , accept
    -- * Misc
  , toDot
  ) where

import Prelude hiding (map)

import Automata.Internal (State(..),Dfsa(..),composeMapping,composeMappingLimited)
import Automata.Internal.Transducer (Dfst(..),MotionDfst(..),Edge(..),EdgeDest(..))
import Control.Applicative (liftA2)
import Control.Monad.ST (runST)
import Data.ByteString (ByteString)
import Data.Foldable (foldl',for_)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Data.Primitive (Array,indexArray,sizeofArray)
import Data.Semigroup (Last(..))
import Data.Set (Set)

import qualified Data.ByteString.Char8 as BC
import qualified Data.List as L
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Strict as M
import qualified Data.Primitive as P
import qualified Data.Primitive.Contiguous as C
import qualified Data.Semigroup as SG
import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified GHC.Exts as E

-- TODO: Minimize DFST using Choffrut's algorithm as described in
-- https://www.irif.fr/~jep/PDF/Exposes/Sequential.pdf. Original
-- description of algorithm given in
--   C. Choffrut, Minimizing subsequential transducers: a survey,
--   Theoret. Comp. Sci. 292 (2003), 131–143.
-- This would give us a meaningful Eq instance, which would let us
-- do better property-testing on DFST.

-- | The number of states, also known as the _order_ of the graph
-- corresponding to the transducer.
states :: Dfsa t -> Int
states (Dfsa t _) = P.sizeofArray t

-- | The number of transitions, also known as the _size_ of the graph
-- corresponding to the automaton. Be careful when interpreting this
-- number. There may be multiple transitions from one state to another
-- when either of the following conditions are met:
--
-- * The range of input causing this transition is non-contiguous.
-- * A transition has unequal outputs associated with two
--   contiguous ranges that border one another.
transitions :: Dfsa t -> Int
transitions (Dfsa t _) = foldl'
  ( \acc m -> acc + DM.size m
  ) 0 t

-- | Map over the output tokens.
map :: Eq n => (m -> n) -> Dfst t m -> Dfst t n
map f (Dfst t m) =
  -- Revisit this implementation if we ever start supporting the canonization
  -- and minimization of DFST.
  Dfst (fmap (DM.map (\(MotionDfst s x) -> MotionDfst s (f x))) t) m

-- | Rejects all input, producing the monoidal identity as its output.
rejection :: (Bounded t, Monoid m) => Dfst t m
rejection = Dfst (C.singleton (DM.pure (MotionDfst 0 mempty))) SU.empty

-- | Union two finite state transducers. Roughly, what it does is:
--
-- 1. Compute the equivalent DFSA. That is, eliminate the output tapes
--    and minimize the resulting DFSA, keeping track of which states from
--    an original transducer map to which states in the corresponding
--    automaton.
-- 2. Union the two automata (synchronous composition).
-- 3. Reintroduce the states from the original transducers, monoidally
--    appending outputs when a transition corresponds to more than
--    one output.
--
-- The new transducer can only accept input that either of the original
-- two could accept. However, there is non-intuitive (but well-defined)
-- behavior that emerges. States that appear unequal can be combined by
-- this function because of pass that discards output.
union :: forall t m. (Ord t, Bounded t, Enum t, Monoid m)
  => Dfst t m -> Dfst t m -> Dfst t m
union a@(Dfst _ax _) b@(Dfst _bx _) =
  let (mapping, dfsa) = composeMapping (||) (unsafeToDfsa a) (unsafeToDfsa b)
   in unionCommon a b dfsa mapping

-- unions :: forall t m. (Ord t, Bounded t, Enum t, Monoid m, Foldable f)
--   => f (Dfst t m) -> Dfst t m
-- unions

-- | Variant of 'union' that accepts an upper bound on the number
-- of states to consider.
boundedUnion :: forall t m. (Ord t, Bounded t, Enum t, Monoid m)
  => Int -- ^ Upper bound on number of states
  -> Dfst t m
  -> Dfst t m
  -> Maybe (Dfst t m)
boundedUnion !maxStates a b = do
  (mapping, dfsa) <- composeMappingLimited maxStates (||) (unsafeToDfsa a) (unsafeToDfsa b)
  Just (unionCommon a b dfsa mapping)

unionCommon :: forall t m. (Ord t, Bounded t, Enum t, Monoid m)
  => Dfst t m
  -> Dfst t m
  -> Dfsa t
  -> Map (Int,Int) Int
  -> Dfst t m
unionCommon (Dfst ax _) (Dfst bx _) (Dfsa t0 f) mapping =
  -- The revMapping goes from a new state to all a-b old state pairs.
  let revMapping :: Map Int (Set (Int,Int))
      revMapping = M.foldlWithKey' (\acc k v -> M.insertWith (<>) v (S.singleton k) acc) M.empty mapping
      t1 :: Array (DM.Map t (MotionDfst m))
      t1 = C.imap
        (\source m -> DM.mapBijection
          (\dest ->
            let oldSources = fromMaybe (error "Automata.Nfst.toDfst: missing old source") (M.lookup source revMapping)
                oldDests = fromMaybe (error "Automata.Nfst.toDfst: missing old dest") (M.lookup dest revMapping)
                -- Do we need to deal with epsilon stuff in here? I don't think so.
                newOutput = foldMap
                  (\(oldSourceA,oldSourceB) -> mconcat $ E.toList $ do
                    MotionDfst oldDestA outA <- DM.elems (indexArray ax oldSourceA)
                    MotionDfst oldDestB outB <- DM.elems (indexArray bx oldSourceB)
                    if S.member (oldDestA,oldDestB) oldDests then pure (outA <> outB) else mempty
                  ) oldSources
             in MotionDfst dest newOutput
          ) m
        ) t0
   in Dfst t1 f

-- | Returns @Nothing@ if the transducer did not end up in an
--   accepting state. Returns @Just@ if it did. The array of
--   output tokens always matches the length of the input.
evaluate :: (Foldable f, Ord t) => Dfst t m -> f t -> Maybe (Array m)
evaluate (Dfst theTransitions finals) tokens =
  let !(!finalState,!totalSize,!allOutput) = foldl'
        (\(!active,!sz,!output) token ->
          let MotionDfst nextState outputToken = DM.lookup token (indexArray theTransitions active)
           in (nextState,sz + 1,outputToken : output)
        ) (0,0,[]) tokens
   in if SU.member finalState finals
        then Just (C.unsafeFromListReverseN totalSize allOutput)
        else Nothing

evaluateAscii :: forall m. Ord m => Dfst Char m -> ByteString -> Maybe (Array m)
evaluateAscii (Dfst theTransitions finals) !tokens =
  let !(!finalState,!allOutput) = BC.foldl'
        (\(!active,!output) token ->
          let MotionDfst nextState outputToken = DM.lookup token (indexArray theTransitions active)
           in (nextState,outputToken : output)
        ) (0,[]) tokens
   in if SU.member finalState finals
        then Just (C.unsafeFromListReverseN (BC.length tokens) allOutput)
        else Nothing

newtype Builder t m s a = Builder (Int -> [Edge t m] -> [Int] -> Result t m a)
  deriving stock (Functor)

data Result t m a = Result !Int ![Edge t m] ![Int] a
  deriving stock (Functor)

instance Applicative (Builder t m s) where
  pure a = Builder (\i es fs -> Result i es fs a)
  Builder f <*> Builder g = Builder $ \i es fs -> case f i es fs of
    Result i' es' fs' x -> case g i' es' fs' of
      Result i'' es'' fs'' y -> Result i'' es'' fs'' (x y)

instance Monad (Builder t m s) where
  Builder f >>= g = Builder $ \i es fs -> case f i es fs of
    Result i' es' fs' a -> case g a of
      Builder g' -> g' i' es' fs'

instance Semigroup a => Semigroup (Builder t m s a) where
  (<>) = liftA2 (SG.<>)

instance (Monoid a, Semigroup a) => Monoid (Builder t m s a) where
  mempty = pure mempty
  mappend = (SG.<>)

-- | Generate a new state in the NFA. On any input, the state transitions to
--   the start state.
state :: Builder t m s (State s)
state = Builder $ \i edges final ->
  Result (i + 1) edges final (State i)

-- | Mark a state as being an accepting state.
accept :: State s -> Builder t m s ()
accept (State n) = Builder $ \i edges final -> Result i edges (n : final) ()

-- | Add a transition from one state to another when the input token
--   is inside the inclusive range. If multiple transitions from
--   a state are given, the last one given wins.
transition ::
     t -- ^ inclusive lower bound
  -> t -- ^ inclusive upper bound
  -> m -- ^ output token
  -> State s -- ^ from state
  -> State s -- ^ to state
  -> Builder t m s ()
transition lo hi output (State source) (State dest) =
  Builder $ \i edges final -> Result i (Edge source dest lo hi output : edges) final ()

-- | This does the same thing as 'build' except that you get to create a
--   default state (distinct from the start state) that is used when a
--   transition does not cover every token. With 'build', the start state
--   is used for this, but it is often desirable to have a different state
--   for this purpose.
buildDefaulted :: forall t m a. (Bounded t, Ord t, Enum t, Monoid m, Ord m)
  => (forall s. State s -> State s -> Builder t m s a)
  -> Dfst t m
buildDefaulted fromStartAndDefault =
  case do { (start, def) <- liftA2 (,) state state; _ <- fromStartAndDefault start def; pure def;} of
    Builder f -> case f 0 [] [] of
      Result totalStates edges final (State def) ->
        internalBuild totalStates edges final def

-- | The argument function turns a start state into an NFST builder. This
-- function converts the builder to a usable transducer.
build :: forall t m a. (Bounded t, Ord t, Enum t, Monoid m, Ord m) => (forall s. State s -> Builder t m s a) -> Dfst t m
build fromStartState =
  case state >>= fromStartState of
    Builder f -> case f 0 [] [] of
      Result totalStates edges final _ ->
        internalBuild totalStates edges final 0

internalBuild :: forall t m. (Bounded t, Ord t, Enum t, Monoid m, Ord m)
  => Int -> [Edge t m] -> [Int] -> Int -> Dfst t m
internalBuild totalStates edges final def =
  let ts0 = runST $ do
        theTransitions <- C.replicateMutable totalStates (DM.pure Nothing)
        outbounds <- C.replicateMutable totalStates []
        for_ edges $ \(Edge source destination lo hi output) -> do
          edgeDests0 <- C.read outbounds source
          let !edgeDests1 = EdgeDest destination lo hi output : edgeDests0
          C.write outbounds source edgeDests1
        (outbounds' :: Array [EdgeDest t m]) <- C.unsafeFreeze outbounds
        flip C.imapMutable' theTransitions $ \i _ ->
          let dests = C.index outbounds' i
           in mconcat
                ( L.map
                  (\(EdgeDest dest lo hi output) ->
                    DM.singleton mempty lo hi (Just (Last (MotionDfst dest output)))
                  )
                  dests
                )
        C.unsafeFreeze theTransitions
   in Dfst (fmap (DM.map (maybe (MotionDfst def mempty) getLast)) ts0) (SU.fromList final)

-- collapse :: Dfst t m -> Dfst t m
-- collapse = MotionDfst

-- Convert a DFST to a DFSA. However, the DFSA is not necessarily minimal, so
-- equality on it is incorrect. Its states have a one-to-one mapping with the
-- states on the DFST.
unsafeToDfsa :: Dfst t m -> Dfsa t
unsafeToDfsa (Dfst t f) = Dfsa (fmap (DM.map motionDfstState) t) f

toDot :: (Bounded t, Enum t) => (t -> t -> m -> String) -> Dfst t m -> String
toDot makeLabel (Dfst ts fs) = concat $
  [ "digraph D {\n" ]
  ++
  dotNodes (sizeofArray ts - 1) fs
  ++
  (do (src,motions) <- zip (enumFrom (0 :: Int)) (E.toList ts)
      dotSourceEdges makeLabel src motions
  )
  ++
  [ "}\n" ]

dotNodes :: Int -> SU.Set Int -> [String]
dotNodes n fs = if n >= 0
  then ("  N" ++ show n ++ " [shape=" ++ (if SU.member n fs then "circle" else "square") ++ "];\n") : dotNodes (n - 1) fs
  else []

dotSourceEdges :: (Bounded t, Enum t) => (t -> t -> m -> String) -> Int -> DM.Map t (MotionDfst m) -> [String]
dotSourceEdges makeLabel src dsts = DM.foldrWithKey
  (\lo hi motion xs -> dotEdge makeLabel src lo hi motion : xs) [] dsts

dotEdge :: (t -> t -> m -> String) -> Int -> t -> t -> MotionDfst m -> String
dotEdge makeLabel src lo hi (MotionDfst dst output) =
  "  N" ++ show src ++ " -> N" ++ show dst ++ " [label=\"" ++ makeLabel lo hi output ++ "\"];\n"

