{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language MagicHash #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language UnboxedTuples #-}

module Automata.Dfsa
  ( -- * Static
    -- ** Types
    Dfsa
    -- ** Evaluation
  , evaluate
  , evaluatePrimArray
    -- ** Properties
  , order
  , size
    -- ** Predicates
  , null
  , universal
  , subsumes
  , disjoint
    -- ** Composition
  , union
  , intersection
    -- ** Special DFA
  , acceptance
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

import Prelude hiding (null)

import Automata.Internal (Dfsa(..),State(..),union,intersection,acceptance,rejection,minimize)
import Control.Applicative (liftA2)
import Data.Foldable (foldl',for_)
import Data.Primitive (Array,PrimArray,Prim)
import Data.Semigroup (Last(..))
import Control.Monad.ST (runST)

import qualified Data.Primitive as P
import qualified Data.Primitive.Contiguous as C
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Set.Unboxed as SU
import qualified GHC.Exts as E

-- | Evaluate a foldable collection of tokens against the DFA. This
-- returns true if the string is accepted by the language.
evaluate :: (Foldable f, Ord t) => Dfsa t -> f t -> Bool
evaluate (Dfsa transitions finals) tokens = SU.member
  (foldl' (\(active :: Int) token -> DM.lookup token (C.index transitions active)) 0 tokens)
  finals

-- | Evaluate a foldable collection of tokens against the DFA. This
-- returns true if the string is accepted by the language.
evaluatePrimArray :: (Prim t, Ord t) => Dfsa t -> PrimArray t -> Bool
evaluatePrimArray (Dfsa transitions finals) tokens = SU.member
  (C.foldl' (\(active :: Int) token -> DM.lookup token (C.index transitions active)) 0 tokens)
  finals

-- | The number of states. The name _order_ comes from graph theory,
-- where the order of a graph is the cardinality of the set of vertices.
order :: Dfsa t -> Int
order (Dfsa t _) = P.sizeofArray t

-- | The number of transitions. The name _size_ comes from graph theory,
-- where the size of a graph is the cardinality of the set of edges. Be
-- careful when interpreting this number. There may be multiple transitions
-- from one state to another when the range of input causing this transition
-- is non-contiguous.
size :: Dfsa t -> Int
size (Dfsa t _) = foldl'
  ( \acc m -> acc + DM.size m
  ) 0 t

-- | Does the DFSA reject all strings?
null :: (Bounded t, Eq t) => Dfsa t -> Bool
null = (== rejection)

-- | Does the DFSA accept all strings?
universal :: (Bounded t, Eq t) => Dfsa t -> Bool
universal = (== acceptance)

-- | Does the first argument accept all strings that the second argument accepts?
-- More precisely:
--
-- > x `subsumes` y ⇔ (∀s. evaluate y s ⇒ evaluate x s)
subsumes :: (Ord t, Bounded t, Enum t) => Dfsa t -> Dfsa t -> Bool
subsumes x y = x == union x y

-- | If the two DFSA accept any of the same strings, returns 'False'. Otherwise,
-- the sets of accepted strings are disjoint, and this returns 'True'. More
-- precisely:
--
-- > disjoint x y ⇔ (∀s. ¬(evaluate x s ∧ evaluate y s))
disjoint :: (Ord t, Bounded t, Enum t) => Dfsa t -> Dfsa t -> Bool
disjoint x y = intersection x y == rejection

newtype Builder t s a = Builder (Int -> [Edge t] -> [Int] -> Result t a)
  deriving stock (Functor)

instance Applicative (Builder t s) where
  pure a = Builder (\i es fs -> Result i es fs a)
  Builder f <*> Builder g = Builder $ \i es fs -> case f i es fs of
    Result i' es' fs' x -> case g i' es' fs' of
      Result i'' es'' fs'' y -> Result i'' es'' fs'' (x y)

instance Monad (Builder t s) where
  Builder f >>= g = Builder $ \i es fs -> case f i es fs of
    Result i' es' fs' a -> case g a of
      Builder g' -> g' i' es' fs'

data Result t a = Result !Int ![Edge t] ![Int] a
  deriving stock (Functor)

data Edge t = Edge !Int !Int !t !t

data EdgeDest t = EdgeDest !Int t t

-- | The argument function takes a start state and builds an NFA. This
-- function will execute the builder. Unspecified transitions move to
-- the start state.
build :: forall t a. (Bounded t, Ord t, Enum t)
  => (forall s. State s -> Builder t s a) -> Dfsa t
build fromStartState =
  case state >>= fromStartState of
    Builder f -> case f 0 [] [] of
      Result totalStates edges final _ ->
        internalBuild totalStates edges final 0

-- | This does the same thing as 'build' except that you get to create a
--   default state (distinct from the start state) that is used when a
--   transition does not cover every token. With 'build', the start state
--   is used for this, but it is often desirable to have a different state
--   for this purpose.
buildDefaulted :: forall t a. (Bounded t, Ord t, Enum t)
  => (forall s. State s -> State s -> Builder t s a)
  -> Dfsa t
buildDefaulted fromStartAndDefault =
  case do { (start, def) <- liftA2 (,) state state; _ <- fromStartAndDefault start def; pure def;} of
    Builder f -> case f 0 [] [] of
      Result totalStates edges final (State def) ->
        internalBuild totalStates edges final def

-- | The argument function takes a start state and builds an NFA. This
-- function will execute the builder.
internalBuild :: forall t. (Bounded t, Ord t, Enum t)
  => Int -> [Edge t] -> [Int] -> Int -> Dfsa t
internalBuild totalStates edges final def =
  let ts = runST $ do
        transitions <- C.replicateMutable totalStates (DM.pure Nothing)
        outbounds <- C.replicateMutable totalStates []
        for_ edges $ \(Edge source destination lo hi) -> do
          edgeDests0 <- C.read outbounds source
          let !edgeDests1 = EdgeDest destination lo hi : edgeDests0
          C.write outbounds source edgeDests1
        (outbounds' :: Array [EdgeDest t]) <- C.unsafeFreeze outbounds
        flip C.imapMutable' transitions $ \i _ ->
          let dests = C.index outbounds' i
           in mconcat
                ( map
                  (\(EdgeDest dest lo hi) -> DM.singleton Nothing lo hi (Just (Last dest)))
                  dests
                )
        C.unsafeFreeze transitions
   in minimize (fmap (DM.map (maybe def getLast)) ts) (SU.fromList final)

-- | Generate a new state in the NFA. On any input, the state transitions to
--   the start state.
state :: Builder t s (State s)
state = Builder $ \i edges final ->
  Result (i + 1) edges final (State i)

-- | Mark a state as being an accepting state.
accept :: State s -> Builder t s ()
accept (State n) = Builder $ \i edges final -> Result i edges (n : final) ()

-- | Add a transition from one state to another when the input token
--   is inside the inclusive range. If multiple transitions from
--   a state are given, the last one given wins.
transition ::
     t -- ^ inclusive lower bound
  -> t -- ^ inclusive upper bound
  -> State s -- ^ from state
  -> State s -- ^ to state
  -> Builder t s ()
transition lo hi (State source) (State dest) =
  Builder $ \i edges final -> Result i (Edge source dest lo hi : edges) final ()

toDot :: (Bounded t, Enum t) => (t -> t -> String) -> Dfsa t -> String
toDot makeLabel (Dfsa ts fs) = concat $
  [ "digraph D {\n" ]
  ++
  dotNodes (P.sizeofArray ts - 1) fs
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

dotSourceEdges :: (Bounded t, Enum t) => (t -> t -> String) -> Int -> DM.Map t Int -> [String]
dotSourceEdges makeLabel src dsts = DM.foldrWithKey
  (\lo hi motion xs -> dotEdge makeLabel src lo hi motion : xs) [] dsts

dotEdge :: (t -> t -> String) -> Int -> t -> t -> Int -> String
dotEdge makeLabel src lo hi dst =
  "  N" ++ show src ++ " -> N" ++ show dst ++ " [label=\"" ++ makeLabel lo hi ++ "\"];\n"

