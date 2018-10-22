{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language MagicHash #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language UnboxedTuples #-}

module Automata.Dfst
  ( -- * Static
    -- ** Types
    Dfst
    -- ** Functions
  , evaluate
  , union
  , map
    -- * Builder
    -- ** Types
  , Builder
  , State
    -- ** Functions
  , build
  , state
  , transition
  , accept
  ) where

import Prelude hiding (map)

import Automata.Internal (State(..),Dfsa(..),composeMapping)
import Automata.Internal.Transducer (Dfst(..),MotionDfst(..),Edge(..),EdgeDest(..))
import Control.Monad.ST (runST)
import Data.Foldable (foldl',for_)
import Data.Primitive (Array,indexArray)
import Data.Semigroup (Last(..))
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Maybe (fromMaybe)

import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Primitive.Contiguous as C
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Set.Unboxed as SU
import qualified GHC.Exts as E

-- | Map over the output tokens.
map :: Eq n => (m -> n) -> Dfst t m -> Dfst t n
map f (Dfst t m) =
  -- Revisit this implementation if we ever start supporting the canonization
  -- and minimization of DFST.
  Dfst (fmap (DM.map (\(MotionDfst s x) -> MotionDfst s (f x))) t) m

union :: forall t m. (Ord t, Bounded t, Enum t, Monoid m) => Dfst t m -> Dfst t m -> Dfst t m
union a@(Dfst ax _) b@(Dfst bx _) =
  let (mapping, Dfsa t0 f) = composeMapping (||) (unsafeToDfsa a) (unsafeToDfsa b)
      -- The revMapping goes from a new state to all a-b old state pairs.
      revMapping :: Map Int (Set (Int,Int))
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
evaluate (Dfst transitions finals) tokens =
  let !(!finalState,!totalSize,!allOutput) = foldl'
        (\(!active,!sz,!output) token ->
          let MotionDfst nextState outputToken = DM.lookup token (indexArray transitions active)
           in (nextState,sz + 1,outputToken : output)
        ) (0,0,[]) tokens
   in if SU.member finalState finals
        then Just (C.unsafeFromListReverseN totalSize allOutput)
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

-- | The argument function turns a start state into an NFST builder. This
-- function converts the builder to a usable transducer.
build :: forall t m a. (Bounded t, Ord t, Enum t, Monoid m, Ord m) => (forall s. State s -> Builder t m s a) -> Dfst t m
build fromStartState =
  case state >>= fromStartState of
    Builder f -> case f 0 [] [] of
      Result totalStates edges final _ ->
        let ts0 = runST $ do
              transitions <- C.replicateM totalStates (DM.pure Nothing)
              outbounds <- C.replicateM totalStates []
              for_ edges $ \(Edge source destination lo hi output) -> do
                edgeDests0 <- C.read outbounds source
                let !edgeDests1 = EdgeDest destination lo hi output : edgeDests0
                C.write outbounds source edgeDests1
              (outbounds' :: Array [EdgeDest t m]) <- C.unsafeFreeze outbounds
              flip C.imapMutable' transitions $ \i _ -> 
                let dests = C.index outbounds' i
                 in mconcat
                      ( L.map
                        (\(EdgeDest dest lo hi output) ->
                          DM.singleton mempty lo hi (Just (Last (MotionDfst dest output)))
                        )
                        dests
                      )
              C.unsafeFreeze transitions
         in Dfst (fmap (DM.map (maybe (MotionDfst 0 mempty) getLast)) ts0) (SU.fromList final)

-- collapse :: Dfst t m -> Dfst t m
-- collapse = MotionDfst 

-- Convert a DFST to a DFSA. However, the DFSA is not necessarily minimal, so
-- equality on it is incorrect. Its states have a one-to-one mapping with the
-- states on the DFST.
unsafeToDfsa :: Dfst t m -> Dfsa t
unsafeToDfsa (Dfst t f) = Dfsa (fmap (DM.map motionDfstState) t) f



