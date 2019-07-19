{-# language BangPatterns #-}
{-# language GADTs #-}
{-# language ScopedTypeVariables #-}

module Automata.Dfsa.Unboxed
  ( Dfsa
  , evaluate
  , evaluatePrimArray
  , evaluateAscii
  , evaluateUtf8
  , fromLifted
  ) where

import Data.Bytes (Bytes,AsciiException,Utf8Exception)
import Data.Primitive (Array,PrimArray,Prim)
import Data.Foldable (foldl')

import qualified Automata.Internal as I
import qualified Data.Primitive.Contiguous as C
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Interval.DBTSUU as DMU
import qualified Data.Bytes as Bytes

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

-- | If this encounters a non-ascii byte, returns @Left@ with the
--   non-ascii byte that was encountered.
evaluateAscii :: Dfsa Char -> Bytes -> Either AsciiException Bool
evaluateAscii (Dfsa transitions finals) !tokens = do
  terminal <- Bytes.foldlAscii'
    (\active token -> DMU.lookup token (C.index transitions active))
    0 tokens
  Right (SU.member terminal finals)

-- | If this encounters a non-utf8 byte sequence, returns @Left@ with the
--   non-ascii byte that was encountered.
evaluateUtf8 :: Dfsa Char -> Bytes -> Either Utf8Exception Bool
evaluateUtf8 (Dfsa transitions finals) !tokens = case e of
  Bytes.Utf8StateSequence err -> Left (Bytes.Utf8ExceptionSequence err)
  Bytes.Utf8StateEndOfInput i -> case i of
    Bytes.Utf8EndOfInput0 terminal -> Right (SU.member terminal finals)
    Bytes.Utf8EndOfInput1 w1 _ ->
      Left (Bytes.Utf8ExceptionEndOfInput (Bytes.Utf8EndOfInput1 w1 ()))
    Bytes.Utf8EndOfInput2 w1 w2 _ ->
      Left (Bytes.Utf8ExceptionEndOfInput (Bytes.Utf8EndOfInput2 w1 w2 ()))
    Bytes.Utf8EndOfInput3 w1 w2 w3 _ ->
      Left (Bytes.Utf8ExceptionEndOfInput (Bytes.Utf8EndOfInput3 w1 w2 w3 ()))
  where
  e = Bytes.foldlUtf8'
    (\active token -> DMU.lookup token (C.index transitions active))
    0 tokens
