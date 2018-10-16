{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}

module Automata.Nfst
  ( -- * Types
    Nfst
    -- * Functions
  , evaluate
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

import Automata.Internal (State(..),Epsilon(..))
import Automata.Internal.Transducer (Nfst(..),TransitionNfst(..),epsilonClosure)
import Control.Monad.ST (runST)
import Data.Set (Set)
import Data.Map.Strict (Map)
import Data.Primitive (Array)
import Data.Foldable (for_)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Lifted.Unlifted as MLN
import qualified Data.Primitive.Contiguous as C
import qualified Data.Foldable as F

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
    ( \xs state outputSets -> MLN.foldlWithKey'
        (\zs outputTokenNext nextStates -> M.unionsWith (<>) (map (\s -> M.singleton s (S.mapMonotonic (outputTokenNext:) outputSets)) (SU.toList nextStates)) : zs)
        xs
        (DM.lookup token (transitionNfstConsume (C.index transitions state)))
    ) [] active

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

data Edge t m = Edge !Int !Int !t !t !m

data EdgeDest t m = EdgeDest !Int !t !t !m

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
              transitions <- C.replicateM totalStates (TransitionNfst SU.empty (DM.pure mempty))
              outbounds <- C.replicateM totalStates []
              epsilonArr <- C.replicateM totalStates []
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
