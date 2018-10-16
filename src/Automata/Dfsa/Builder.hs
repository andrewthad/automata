{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}

module Automata.Dfsa.Builder
  ( Builder
  , run
  , state
  , transition
  , accept
  ) where

import Automata.Internal (Dfsa,minimize)
import Control.Monad.ST (runST)
import Data.Foldable (for_)
import Data.Primitive (Array)
import Data.Semigroup (Last(..))
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Primitive.Contiguous as C
import qualified Data.Set.Unboxed as SU

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

newtype State s = State Int

-- | The argument function takes a start state and builds an NFA. This
-- function will execute the builder.
run :: forall t a. (Bounded t, Ord t, Enum t) => (forall s. State s -> Builder t s a) -> Dfsa t
run fromStartState =
  case state >>= fromStartState of
    Builder f -> case f 0 [] [] of
      Result totalStates edges final _ ->
        let ts = runST $ do
              transitions <- C.replicateM totalStates (DM.pure Nothing)
              outbounds <- C.replicateM totalStates []
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
         in minimize (fmap (DM.map (maybe 0 getLast)) ts) (SU.fromList final)
  
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


