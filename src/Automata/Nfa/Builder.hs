{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}

module Automata.Nfa.Builder
  ( Builder
  , run
  , state
  , transition
  , accept
  , epsilon
  ) where

import Automata.Internal (Nfa(..),TransitionNfa(..))
import Control.Monad.ST (runST)
import Data.Foldable (for_)
import Data.Primitive (Array)
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Primitive.Contiguous as C
import qualified Data.Set.Unboxed as SU

newtype Builder t s a = Builder (Int -> [Edge t] -> [Epsilon] -> [Int] -> Result t a)
  deriving stock (Functor)

instance Applicative (Builder t s) where
  pure a = Builder (\i es eps fs -> Result i es eps fs a)
  Builder f <*> Builder g = Builder $ \i es eps fs -> case f i es eps fs of
    Result i' es' eps' fs' x -> case g i' es' eps' fs' of
      Result i'' es'' eps'' fs'' y -> Result i'' es'' eps'' fs'' (x y)

instance Monad (Builder t s) where
  Builder f >>= g = Builder $ \i es eps fs -> case f i es eps fs of
    Result i' es' eps' fs' a -> case g a of
      Builder g' -> g' i' es' eps' fs'

data Result t a = Result !Int ![Edge t] ![Epsilon] ![Int] a
  deriving stock (Functor)

data Edge t = Edge !Int !Int !t !t

data EdgeDest t = EdgeDest !Int t t

data Epsilon = Epsilon !Int !Int

newtype State s = State Int

-- | The argument function takes a start state and builds an NFA. This
-- function will execute the builder.
run :: forall t a. (Bounded t, Ord t, Enum t) => (forall s. State s -> Builder t s a) -> Nfa t
run fromStartState =
  case state >>= fromStartState of
    Builder f -> case f 0 [] [] [] of
      Result totalStates edges epsilons final _ ->
        let ts = runST $ do
              transitions <- C.replicateM totalStates (TransitionNfa SU.empty (DM.pure SU.empty))
              outbounds <- C.replicateM totalStates []
              epsilonArr <- C.replicateM totalStates []
              for_ epsilons $ \(Epsilon source destination) -> do
                edgeDests0 <- C.read epsilonArr source
                let !edgeDests1 = destination : edgeDests0
                C.write epsilonArr source edgeDests1
              (epsilonArr' :: Array [Int]) <- C.unsafeFreeze epsilonArr
              for_ edges $ \(Edge source destination lo hi) -> do
                edgeDests0 <- C.read outbounds source
                let !edgeDests1 = EdgeDest destination lo hi : edgeDests0
                C.write outbounds source edgeDests1
              (outbounds' :: Array [EdgeDest t]) <- C.unsafeFreeze outbounds
              flip C.imapMutable' transitions $ \i (TransitionNfa _ _) -> 
                let dests = C.index outbounds' i
                    eps = C.index epsilonArr' i
                 in TransitionNfa (SU.fromList eps)
                      ( mconcat
                        ( map
                          (\(EdgeDest dest lo hi) -> DM.singleton SU.empty lo hi (SU.singleton dest))
                          dests
                        )
                      )
              C.unsafeFreeze transitions
         in Nfa ts (SU.fromList final)
  
-- | Generate a new state in the NFA. On any input, the
--   state transitions to zero states.
state :: Builder t s (State s)
state = Builder $ \i edges eps final -> Result (i + 1) edges eps final (State i)

-- | Mark a state as being an accepting state. 
accept :: State s -> Builder t s ()
accept (State n) = Builder $ \i edges eps final -> Result i edges eps (n : final) ()

-- | Add a transition from one state to another when the input token
--   is inside the inclusive range.
transition ::
     t -- ^ inclusive lower bound
  -> t -- ^ inclusive upper bound
  -> State s -- ^ from state
  -> State s -- ^ to state
  -> Builder t s ()
transition lo hi (State source) (State dest) =
  Builder $ \i edges eps final -> Result i (Edge source dest lo hi : edges) eps final ()

-- | Add a transition from one state to another that consumes no input.
epsilon ::
     State s -- ^ from state
  -> State s -- ^ to state
  -> Builder t s ()
epsilon (State source) (State dest) = 
  Builder $ \i edges eps final -> Result i edges (if source /= dest then Epsilon source dest : eps else eps) final ()

