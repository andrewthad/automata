{-# language ScopedTypeVariables #-}

module Automata.Dfsa.Unboxed
  ( Dfsa
  , evaluate
  , evaluatePrimArray
  , fromLifted
  ) where

import Data.Primitive (Array,PrimArray,Prim)
import Data.Foldable (foldl')

import qualified Automata.Internal as I
import qualified Data.Primitive.Contiguous as C
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Interval.DBTSLL as DML
import qualified Data.Map.Interval.DBTSUU as DMU

-- | Deterministic Finite-State Automaton. This variant has
-- unboxed keys and values.
data Dfsa t = Dfsa
  !(Array (DMU.Map t Int))
  !(SU.Set Int)
  deriving (Eq,Show)

fromLifted :: Prim t => I.Dfsa t -> Dfsa t
fromLifted (I.Dfsa ts fs) = Dfsa (C.map' DMU.fromLiftedLifted ts) fs

evaluate :: (Foldable f, Prim t, Ord t) => Dfsa t -> f t -> Bool
{-# INLINE evaluate #-}
evaluate (Dfsa transitions finals) tokens = SU.member
  (foldl' (\(active :: Int) token -> DMU.lookup token (C.index transitions active)) 0 tokens)
  finals

evaluatePrimArray :: (Prim t, Ord t) => Dfsa t -> PrimArray t -> Bool
{-# INLINE evaluatePrimArray #-}
evaluatePrimArray (Dfsa transitions finals) tokens = SU.member
  (C.foldl' (\(active :: Int) token -> DMU.lookup token (C.index transitions active)) 0 tokens)
  finals

