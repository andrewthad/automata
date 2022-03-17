{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}

module Automata.Nfsa
  ( -- * Types
    Nfsa
    -- * Conversion
  , toDfsa
  , fromDfsa
    -- * Evaluation
  , evaluate
    -- * Composition
  , AI.append
  , union
    -- * Special NFA
  , rejection
  , AI.empty
    -- * Builder
    -- ** Types
  , BuilderT
  , Builder
  , State
    -- ** Functions
  , build
  , state
  , transition
  , accept
  , epsilon
  ) where

import Automata.Internal
    ( Nfsa(..), Dfsa(..), TransitionNfsa(..), toDfsa, epsilonClosure )
import Data.Foldable ( foldl', for_ )

import qualified Automata.Internal as AI
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Primitive.Contiguous as C
import Control.Monad.ST (runST)
import Data.Primitive (Array)
import Data.Functor.Identity (Identity)
import qualified Data.Semigroup as SG
import Control.Applicative (liftA2)
import Control.Monad.Trans.Class (MonadTrans (lift))

fromDfsa :: Dfsa t -> Nfsa t
fromDfsa (Dfsa t f) =
  Nfsa (fmap (TransitionNfsa SU.empty . DM.mapBijection SU.singleton) t) f

rejection :: Bounded t => Nfsa t
rejection = AI.rejectionNfsa

union :: (Bounded t) => Nfsa t -> Nfsa t -> Nfsa t
union = AI.unionNfsa

-- note: turn foldl' + mconcat into single foldMap?
evaluate :: (Foldable f, Ord t) => Nfsa t -> f t -> Bool
evaluate (Nfsa transitions finals) tokens = not $ SU.null $ SU.intersection
  ( foldl'
    ( \(active :: SU.Set Int) token -> mconcat $ SU.foldl'
      (\xs state -> DM.lookup token (transitionNfsaConsume (C.index transitions state)) : xs)
      ([] :: [SU.Set Int])
      active
    ) (transitionNfsaEpsilon (C.index transitions 0)) tokens
  )
  finals

newtype BuilderT t s m a = BuilderT (Int -> [Edge t] -> [Epsilon] -> [Int] -> m (Result t a))
  deriving stock (Functor)

type Builder t s a = BuilderT t s Identity a

instance Monad m => Applicative (BuilderT t s m) where
  pure a = BuilderT (\i es eps fs -> pure (Result i es eps fs a))
  BuilderT f <*> BuilderT g = BuilderT $ \i es eps fs -> do
    Result i' es' eps' fs' x <- f i es eps fs 
    Result i'' es'' eps'' fs'' y <- g i' es' eps' fs'
    pure $ Result i'' es'' eps'' fs'' (x y)

instance Monad m => Monad (BuilderT t s m) where
  BuilderT f >>= g = BuilderT $ \i es eps fs -> do
    Result i' es' eps' fs' a <-  f i es eps fs
    case g a of
      BuilderT g' -> g' i' es' eps' fs'

instance MonadTrans (BuilderT t s) where
  lift m = BuilderT $ \i es ps is -> Result i es ps is <$> m

instance (Monad f, Semigroup a) => Semigroup (BuilderT t s f a) where
  (<>) = liftA2 (SG.<>)

instance (Monad f, Monoid a) => Monoid (BuilderT t s f a) where
  mempty = pure mempty
  mappend = (SG.<>)

data Result t a = Result !Int ![Edge t] ![Epsilon] ![Int] a
  deriving stock (Functor)

data Edge t = Edge !Int !Int !t !t

data EdgeDest t = EdgeDest !Int !t !t

data Epsilon = Epsilon !Int !Int

newtype State s = State Int

-- | The argument function takes a start state and builds an NFSA. This
-- function will execute the builder.
build :: forall m t a. (Monad m, Bounded t, Ord t, Enum t) => (forall s. State s -> BuilderT t s m a) -> m (Nfsa t)
build fromStartState =
  case state >>= fromStartState of
    BuilderT f -> f 0 [] [] [] >>=
      \(Result totalStates edges epsilons final _) ->
        let ts0 = runST $ do
              transitions <- C.replicateMutable totalStates (TransitionNfsa SU.empty (DM.pure SU.empty))
              outbounds <- C.replicateMutable totalStates []
              epsilonArr <- C.replicateMutable totalStates []
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
              flip C.imapMutable' transitions $ \i (TransitionNfsa _ _) ->
                let dests = C.index outbounds' i
                    eps = C.index epsilonArr' i
                 in TransitionNfsa (SU.fromList eps)
                      ( mconcat
                        ( map
                          (\(EdgeDest dest lo hi) -> DM.singleton SU.empty lo hi (SU.singleton dest))
                          dests
                        )
                      )
              C.unsafeFreeze transitions
            ts1 = C.imap (\s (TransitionNfsa eps consume) -> TransitionNfsa (epsilonClosure ts0 (SU.singleton s <> eps)) (DM.map (epsilonClosure ts0) consume)) ts0
         in pure $ Nfsa ts1 (SU.fromList final)

-- | Generate a new state in the NFA. On any input, the
--   state transitions to zero states.
state :: Monad m => BuilderT t s m (State s)
state = BuilderT $ \i edges eps final -> pure (Result (i + 1) edges eps final (State i))

-- | Mark a state as being an accepting state. 
accept :: Monad m => State s -> BuilderT t s m ()
accept (State n) = BuilderT $ \i edges eps final -> pure (Result i edges eps (n : final) ())

-- | Add a transition from one state to another when the input token
--   is inside the inclusive range.
transition ::
  Monad m =>
     t -- ^ inclusive lower bound
  -> t -- ^ inclusive upper bound
  -> State s -- ^ from state
  -> State s -- ^ to state
  -> BuilderT t s m ()
transition lo hi (State source) (State dest) =
  BuilderT $ \i edges eps final -> pure (Result i (Edge source dest lo hi : edges) eps final ())

-- | Add a transition from one state to another that consumes no input.
epsilon ::
  Monad m =>
     State s -- ^ from state
  -> State s -- ^ to state
  -> BuilderT t s m ()
epsilon (State source) (State dest) =
  BuilderT $ \i edges eps final -> pure (Result i edges (if source /= dest then Epsilon source dest : eps else eps) final ())

