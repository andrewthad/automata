{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
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
  ) where

import Automata.Internal (Nfsa(..),Dfsa(..),TransitionNfsa(..),toDfsa)
import Data.Semigroup (First(..))
import Control.Monad.Trans.State.Strict (State)
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad.ST (runST)
import Data.Primitive (Array,indexArray)
import Data.Foldable (foldl')

import qualified Automata.Internal as AI
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Unboxed.Lifted as MUL
import qualified Data.Primitive.Contiguous as C

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

