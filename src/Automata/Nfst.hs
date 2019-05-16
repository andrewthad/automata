{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}

module Automata.Nfst
  ( -- * Static
    -- ** Types
    Nfst
    -- ** Functions
  , evaluate
  , evaluateAscii
  , union
  , toDfst
  , toNfsa
    -- ** Special Transducers
  , rejection
    -- * Builder
    -- ** Types
  , Builder
  , State
    -- ** Functions
  , build
  , state
  , transition
  , epsilon
  , accept
  ) where

import Automata.Internal (State(..),Epsilon(..),Nfsa(..),Dfsa(..),TransitionNfsa(..),toDfsaMapping)
import Automata.Internal.Transducer (Nfst(..),Dfst(..),TransitionNfst(..),MotionDfst(..),Edge(..),EdgeDest(..),epsilonClosure,rejection,union)
import Control.Monad.ST (runST)
import Data.ByteString (ByteString)
import Data.Foldable (for_)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid (Any(..))
import Data.Primitive (Array,indexArray)
import Data.Set (Set)

import qualified Data.ByteString.Char8 as BC
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Lifted.Unlifted as MLN
import qualified Data.Primitive.Contiguous as C
import qualified Data.Foldable as F

debugTrace :: Show a => a -> a
debugTrace = id

-- | Evaluate an NFST. If the output is the empty set, the input string
-- did not belong to the language. Otherwise, all possible outputs given.
-- The output token lists are in reverse order, and they are all the exact
-- same length as the input string. The reversed order is done to maximize
-- opportunities for sharing common output prefixes. To get the output tokens
-- in the right order, reverse the NFST before evaluating an input string
-- against it. Then, the output tokens will be in the right order, and they will
-- share common suffixes in memory.
evaluate :: forall f t m. (Foldable f, Ord t, Ord m) => Nfst t m -> f t -> Set [m]
evaluate (Nfst transitions finals) tokens = S.unions $ M.elems $ M.filterWithKey
  (\k _ -> SU.member k finals)
  (F.foldl' step (M.unionsWith (<>) (map (\s -> M.singleton s (S.singleton [])) (SU.toList (transitionNfstEpsilon (C.index transitions 0))))) tokens)
  where
  step :: Map Int (Set [m]) -> t -> Map Int (Set [m])
  step active token = M.unionsWith (<>) $ M.foldlWithKey'
    ( \xs theState outputSets -> MLN.foldlWithKey'
        (\zs outputTokenNext nextStates -> M.unionsWith (<>) (map (\s -> M.singleton s (S.mapMonotonic (outputTokenNext:) outputSets)) (SU.toList nextStates)) : zs)
        xs
        (DM.lookup token (transitionNfstConsume (C.index transitions theState)))
    ) [] active

evaluateAscii :: forall m. Ord m => Nfst Char m -> ByteString -> Set [m]
evaluateAscii (Nfst transitions finals) tokens = S.unions $ M.elems $ M.filterWithKey
  (\k _ -> SU.member k finals)
  (BC.foldl' step (M.unionsWith (<>) (map (\s -> M.singleton s (S.singleton [])) (SU.toList (transitionNfstEpsilon (C.index transitions 0))))) tokens)
  where
  step :: Map Int (Set [m]) -> Char -> Map Int (Set [m])
  step active token = M.unionsWith (<>) $ M.foldlWithKey'
    ( \xs theState outputSets -> MLN.foldlWithKey'
        (\zs outputTokenNext nextStates -> M.unionsWith (<>) (map (\s -> M.singleton s (S.mapMonotonic (outputTokenNext:) outputSets)) (SU.toList nextStates)) : zs)
        xs
        (DM.lookup token (transitionNfstConsume (C.index transitions theState)))
    ) [] active

-- | Convert an NFST to a DFST that accepts the same input and produces
--   output. Since NFST are more powerful than DFST, it is not possible
--   to preserve output of the NFST during this conversion. However,
--   this function makes the guarantee that if the NFST would accepts
--   an input string and produces the output
--
--   > [[a1,a2,a3,...],[b1,b2,b3,...],...]
--
--   Then DFST will accept the same input and produce an output of
--
--   > ∃ ω1 ω2. [ω1 <> a1 <> b1 <> ..., ω2 <> a1 <> b1 <> ...]
--
--   This must be a commutative semigroup, and the existentially
--   quantified values appended to the output cannot be easily
--   predicted.
toDfst :: forall t m. (Ord t, Bounded t, Enum t, Monoid m) => Nfst t m -> Dfst t m
toDfst x@(Nfst tx _) =
  let (mapping,Dfsa t0 f) = toDfsaMapping (toNfsa x)
      mapping' = debugTrace mapping
      -- The revMapping goes from new state id to a set of old state subsets
      revMapping :: Map Int (SU.Set Int)
      revMapping = debugTrace $ M.foldlWithKey' (\acc k v -> M.insertWith (<>) v k acc) M.empty mapping'
      t1 = C.imap
        (\source m -> DM.mapBijection
          (\dest ->
            let oldSources = fromMaybe (error "Automata.Nfst.toDfst: missing old source") (M.lookup source revMapping)
                oldDests = fromMaybe (error "Automata.Nfst.toDfst: missing old dest") (M.lookup dest revMapping)
                -- Do we need to deal with epsilon stuff in here? I don't think so.
                -- Also, this part could be greatly improved. We are using a very simple heuristic,
                -- and we could prune out far more outputs if we were more clever about this.
                newOutput = SU.foldMap (\oldSource -> DM.foldMap (MLN.foldMapWithKey' (\output oldDestStates -> if getAny (SU.foldMap (\oldDest -> Any (SU.member oldDest oldDests)) oldDestStates) then output else mempty)) (transitionNfstConsume (indexArray tx oldSource))) oldSources
             in MotionDfst dest newOutput
          ) m
        ) t0
   in Dfst t1 f

-- | Discard information about output tokens.
toNfsa :: Nfst t m -> Nfsa t
toNfsa (Nfst t f) = Nfsa
  (fmap (\(TransitionNfst eps m) -> TransitionNfsa eps (DM.map (MLN.foldlWithKey' (\acc _ x -> acc <> x) mempty) m)) t)
  f

newtype Builder t m s a = Builder (Int -> [Edge t m] -> [Epsilon] -> [Int] -> Result t m a)
  deriving stock (Functor)

data Result t m a = Result !Int ![Edge t m] ![Epsilon] ![Int] a
  deriving stock (Functor)

instance Applicative (Builder t m s) where
  pure a = Builder (\i es eps fs -> Result i es eps fs a)
  Builder f <*> Builder g = Builder $ \i es eps fs -> case f i es eps fs of
    Result i' es' eps' fs' x -> case g i' es' eps' fs' of
      Result i'' es'' eps'' fs'' y -> Result i'' es'' eps'' fs'' (x y)

instance Monad (Builder t m s) where
  Builder f >>= g = Builder $ \i es eps fs -> case f i es eps fs of
    Result i' es' eps' fs' a -> case g a of
      Builder g' -> g' i' es' eps' fs'

-- | Generate a new state in the NFA. On any input, the
--   state transitions to zero states.
state :: Builder t m s (State s)
state = Builder $ \i edges eps final -> Result (i + 1) edges eps final (State i)

-- | Mark a state as being an accepting state. 
accept :: State s -> Builder t m s ()
accept (State n) = Builder $ \i edges eps final -> Result i edges eps (n : final) ()

-- | Add a transition from one state to another when the input token
--   is inside the inclusive range.
transition ::
     t -- ^ inclusive lower bound
  -> t -- ^ inclusive upper bound
  -> m -- ^ output token
  -> State s -- ^ from state
  -> State s -- ^ to state
  -> Builder t m s ()
transition lo hi output (State source) (State dest) =
  Builder $ \i edges eps final -> Result i (Edge source dest lo hi output : edges) eps final ()

-- | Add a transition from one state to another that consumes no input.
--   No output is generated on such a transition.
epsilon ::
     State s -- ^ from state
  -> State s -- ^ to state
  -> Builder t m s ()
epsilon (State source) (State dest) = 
  Builder $ \i edges eps final -> Result i edges (if source /= dest then Epsilon source dest : eps else eps) final ()

-- | The argument function turns a start state into an NFST builder. This
-- function converts the builder to a usable transducer.
build :: forall t m a. (Bounded t, Ord t, Enum t, Monoid m, Ord m) => (forall s. State s -> Builder t m s a) -> Nfst t m
build fromStartState =
  case state >>= fromStartState of
    Builder f -> case f 0 [] [] [] of
      Result totalStates edges epsilons final _ ->
        let ts0 = runST $ do
              transitions <- C.replicateMutable totalStates (TransitionNfst SU.empty (DM.pure mempty))
              outbounds <- C.replicateMutable totalStates []
              epsilonArr <- C.replicateMutable totalStates []
              for_ epsilons $ \(Epsilon source destination) -> do
                edgeDests0 <- C.read epsilonArr source
                let !edgeDests1 = destination : edgeDests0
                C.write epsilonArr source edgeDests1
              (epsilonArr' :: Array [Int]) <- C.unsafeFreeze epsilonArr
              for_ edges $ \(Edge source destination lo hi output) -> do
                edgeDests0 <- C.read outbounds source
                let !edgeDests1 = EdgeDest destination lo hi output : edgeDests0
                C.write outbounds source edgeDests1
              (outbounds' :: Array [EdgeDest t m]) <- C.unsafeFreeze outbounds
              flip C.imapMutable' transitions $ \i (TransitionNfst _ _) -> 
                let dests = C.index outbounds' i
                    eps = C.index epsilonArr' i
                 in TransitionNfst
                      ( SU.fromList eps )
                      ( mconcat
                        ( map
                          (\(EdgeDest dest lo hi output) ->
                            DM.singleton mempty lo hi (MLN.singleton output (SU.singleton dest)) :: DM.Map t (MLN.Map m (SU.Set Int))
                          )
                          dests
                        )
                      )
              C.unsafeFreeze transitions
            ts1 = C.imap (\s (TransitionNfst eps consume) -> TransitionNfst (epsilonClosure ts0 (SU.singleton s <> eps)) (DM.map (MLN.map (epsilonClosure ts0)) consume)) ts0
         in Nfst ts1 (SU.fromList final)
