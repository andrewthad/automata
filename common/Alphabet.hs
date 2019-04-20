{-# language BangPatterns #-}

module Alphabet
  ( once
  , twice
  , twiceAscii
  , liftedAcceptor
  , unboxedAcceptor
  , evaluateOptimally
  ) where

-- This module provides an automaton that accepts input consisting
-- of all the letters of the alphabet in order. This is case-insensitive,
-- and the alphabet may appear an arbitrary number of times, as long as
-- it goes all the way from A to Z each time. See the functions "once"
-- and "twice" for examples of input that should be accepted by this
-- automaton.
--
-- The purpose of this module is to compare the evaluation functions
-- of lifted DFSA and unboxed DFSA. (On the author's computer,
-- evaluating input with the unboxed DFSA runs 8 times faster).
-- This module is imported by both the test suite and the benchmark
-- suite in order to confirm that the automaton actually does what
-- it is expected to.

import Automata.Dfsa (Dfsa)
import Data.Char (toUpper,ord)
import Data.Enum.Types (D(..))
import Data.Primitive (PrimArray(..))
import Data.Word (Word32,Word8)
import Data.Bits ((.|.))

import qualified Automata.Dfsa as Dfsa
import qualified Automata.Dfsa.Unboxed as UnboxedDfsa
import qualified Data.Primitive as PM
import qualified GHC.Exts as E

once :: PrimArray Char
once = E.fromList "aBcDeFgHIJKLMnopqRSTuvWXyZ"

twice :: PrimArray Char
twice = E.fromList twiceString

twiceString :: String
twiceString = "aBcDeFgHIJKLMnopqRSTuvWXyZABCDefGhijkLmNopQRSTuVwXyz"

twiceAscii :: PrimArray Word8
twiceAscii = E.fromList (map (fromIntegral . ord) twiceString)

liftedAcceptor :: Dfsa Char
liftedAcceptor = Dfsa.buildDefaulted $ \start _ -> do
  Dfsa.accept start
  let go !c !old = case compare c 'z' of
        LT -> do
          new <- Dfsa.state
          Dfsa.transition c c old new
          Dfsa.transition (toUpper c) (toUpper c) old new
          go (succ c) new
        EQ -> do
          Dfsa.transition c c old start
          Dfsa.transition (toUpper c) (toUpper c) old start
        GT -> error "liftedAlphabetAcceptor: character greater than z"
  go 'a' start

unboxedAcceptor :: UnboxedDfsa.Dfsa Char
unboxedAcceptor = UnboxedDfsa.fromLifted liftedAcceptor

evaluateOptimally :: PrimArray Char -> Bool
evaluateOptimally (PrimArray a) = evaluateOptimally' (PrimArray a)

evaluateOptimally' :: PrimArray Word32 -> Bool
evaluateOptimally' !arr = go 122 (PM.sizeofPrimArray arr - 1) where
  go :: Word -> Int -> Bool
  go !c !ix = if ix >= 0
    then if word32ToWord (PM.indexPrimArray arr ix) .|. 0x20 == c
      then if c > 97
        then go (c - 1) (ix - 1)
        else go 122 (ix - 1)
      else False
    else c == 122

word32ToWord :: Word32 -> Word
word32ToWord = fromIntegral

