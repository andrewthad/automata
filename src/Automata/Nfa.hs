{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language ScopedTypeVariables #-}

module Automata.Nfa
  ( Nfa(..)
  , append
  , toDfa
  , evaluate
  ) where

import Automata.Internal (Nfa(..),Dfa(..),TransitionNfa(..),toDfa,append,evaluate)
import Data.Semigroup (First(..))
import Control.Monad.Trans.State.Strict (State)
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad.ST (runST)
import Data.Primitive (Array,indexArray)
import Control.Monad (forM_)
import Data.Foldable (foldl')

import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Strict as M
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Unboxed.Lifted as MUL
import qualified Data.Primitive.Contiguous as C
import qualified Data.Primitive as PM

fromDfa :: Dfa t -> Nfa t
fromDfa (Dfa t f) =
  Nfa (fmap (TransitionNfa SU.empty . DM.mapBijection SU.singleton) t) f

