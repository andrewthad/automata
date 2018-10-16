{-# language BangPatterns #-}
{-# language MagicHash #-}
{-# language ScopedTypeVariables #-}
{-# language UnboxedTuples #-}

module Automata.Dfsa
  ( -- * Types
    Dfsa
    -- * Evaluation
  , evaluate
    -- * Composition
  , union
  , intersection
    -- * Special DFA
  , acceptance
  , rejection
  ) where

import Automata.Internal (Dfsa(..),union,intersection,acceptance,rejection)
import Data.Foldable (foldl')

import qualified Data.Primitive.Contiguous as C
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Set.Unboxed as SU

-- | Evaluate a foldable collection of tokens against the DFA. This
-- returns true if the string is accepted by the language.
evaluate :: (Foldable f, Ord t) => Dfsa t -> f t -> Bool
evaluate (Dfsa transitions finals) tokens = SU.member
  (foldl' (\(active :: Int) token -> DM.lookup token (C.index transitions active)) 0 tokens)
  finals


