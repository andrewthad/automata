{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language MagicHash #-}
{-# language BangPatterns #-}

module Automata.Dfst.Compact.Unboxed
  ( -- * Types
    CompactDfst
    -- * Functions
  , fromLifted
  , evaluateUtf8
  , evaluateAscii
    -- * Properties
  , states
  ) where

import Automata.Internal.Transducer (MotionCompactDfst(..))
import Automata.Dfst.Compact (Ranged(..))
import Data.Primitive (PrimArray(..),Prim,Array)
import Data.Bytes (Bytes(..),IndexChar(..),Utf8Exception,AsciiException)
import Data.Bool (bool)
import GHC.Exts (Int(I#),Int#,ByteArray#)
import qualified Data.Bytes as B
import qualified Data.Primitive.Contiguous as C
import qualified Automata.Internal.Transducer as I
import qualified Data.Map.Interval.DBTSUL as DM
import qualified Data.Set.Unboxed as SU
import qualified Data.Primitive as PM

data CompactDfst t m = CompactDfst
  !(Array (TransitionCompactDfst t)) -- transitions
  !(SU.Set Int) -- finals
  !(Array m) -- output tokens

data TransitionCompactDfst t
  = TransitionCompactDfstSingle !(CompactSequence t)
  | TransitionCompactDfstMultiple {-# UNPACK #-} !(DM.Map t MotionCompactDfst)

data CompactSequence t = CompactSequence
  !(PrimArray t) -- sequence of inputs to match, length >= 1
  !Int -- destination after straight-and-narrow path
  !Int -- destination after veering off path
  !Int -- output (as an index) from starting straight-and-narrow path
  !Int -- output (as an index) after veering off path

-- | The number of states. Since a 'CompactDfst' is not backed
-- by a true graph (rather, a graph-like structure), this
-- number lacks a good theoretical foundation, but it is still
-- a useful approximation of the size.
states :: CompactDfst t m -> Int
states (CompactDfst t _ _) = PM.sizeofArray t

fromLifted :: Prim t => I.CompactDfst t m -> CompactDfst t m
fromLifted (I.CompactDfst ts fs outs) = CompactDfst
  (C.map' fromLiftedTransition ts)
  fs
  outs

fromLiftedTransition :: Prim t => I.TransitionCompactDfst t -> TransitionCompactDfst t
fromLiftedTransition (I.TransitionCompactDfstSingle (I.CompactSequence arr a b c d)) =
  TransitionCompactDfstSingle (CompactSequence (C.map id arr) a b c d)
fromLiftedTransition (I.TransitionCompactDfstMultiple x) =
  TransitionCompactDfstMultiple (DM.fromLiftedLifted x)

evaluateUtf8 :: forall m.
     CompactDfst Char m
  -> Bytes
  -> Either Utf8Exception (Maybe (Array (Ranged m)))
evaluateUtf8 (CompactDfst transitions finals outputs) (Bytes tokens s0 len0) =
  case B.indexUtf8 tokens s0 end of
    Left st -> case B.terminate st of
      Left err -> Left err
      Right () -> Right $! bool Nothing (Just mempty) (SU.member 0 finals)
    Right (IndexChar s1 token0) -> case PM.indexArray transitions 0 of
      TransitionCompactDfstSingle (CompactSequence string successState failureState successToken failureToken) ->
        if PM.indexPrimArray string 0 == token0
          -- Sequences are guaranteed to have length >= 1, so this indexing does
          -- not need to be guarded.
          then goSequence string 1 (PM.sizeofPrimArray string) successState failureState failureToken 1 0 successToken 0 [] s1
          else goUnknown failureState 1 0 failureToken 0 [] s1
      TransitionCompactDfstMultiple theMap ->
        let MotionCompactDfst nextState outputTokenIndex = DM.lookup token0 theMap
         in goUnknown nextState 1 0 outputTokenIndex 0 [] s1
  where
  !end = s0 + len0
  goSequence :: PrimArray Char -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> [Ranged m] -> Int -> Either Utf8Exception (Maybe (Array (Ranged m)))
  goSequence !string !stringIx !stringSz !successState !failureState !failureTokenIndex !ix !outputSz !nextOutputTokenIndex !nextOutputStart !output !tokenIxA = case B.indexUtf8 tokens tokenIxA end of
    Left st -> case B.terminate st of
      Left err -> Left err
      Right () -> if stringIx < stringSz
        -- Sequences may not contain final states, so mid-sequence input
        -- termination always indicates an unrecognized input.
        then Right Nothing
        else if SU.member successState finals
          then let !r' = r in Right $! Just $! C.unsafeFromListReverseN (outputSz + 1) (r' : output)
          else Right Nothing
    Right (IndexChar tokenIxB tokenB) -> if stringIx < stringSz
      then if PM.indexPrimArray string stringIx == tokenB
        then goSequence string (stringIx + 1) stringSz successState failureState failureTokenIndex (ix + 1) outputSz nextOutputTokenIndex nextOutputStart output tokenIxB
        else bool
          (let !r' = r in goUnknown failureState (ix + 1) (outputSz + 1) failureTokenIndex ix (r' : output) tokenIxB)
          (goUnknown failureState (ix + 1) outputSz failureTokenIndex nextOutputStart output tokenIxB)
          (nextOutputTokenIndex == failureTokenIndex)
      else goUnknown successState ix outputSz nextOutputTokenIndex nextOutputStart output tokenIxA
    where
    {-# INLINE r #-}
    r = Ranged nextOutputStart (ix - nextOutputStart) (PM.indexArray outputs nextOutputTokenIndex)
  goUnknown :: Int -> Int -> Int -> Int -> Int -> [Ranged m] -> Int -> Either Utf8Exception (Maybe (Array (Ranged m)))
  goUnknown !state !ix !outputSz !nextOutputTokenIndex !nextOutputStart !output !tokenIxA = case B.indexUtf8 tokens tokenIxA end of
    Left st -> case B.terminate st of
      Left err -> Left err
      Right () -> if SU.member state finals
        then let !r' = r in Right $! Just $! C.unsafeFromListReverseN (outputSz + 1) (r' : output)
        else Right Nothing
    Right (IndexChar tokenIxB tokenB) -> case PM.indexArray transitions state of
      TransitionCompactDfstSingle (CompactSequence string successState failureState successTokenIndex failureTokenIndex) ->
        if PM.indexPrimArray string 0 == tokenB
          -- Sequences are guaranteed to have length >= 1, so this indexing does
          -- not need to be guarded.
          then bool
            (let !r' = r in goSequence string 1 (PM.sizeofPrimArray string) successState failureState failureTokenIndex (ix + 1) (outputSz + 1) successTokenIndex ix (r' : output) tokenIxB)
            (goSequence string 1 (PM.sizeofPrimArray string) successState failureState failureTokenIndex (ix + 1) outputSz successTokenIndex nextOutputStart output tokenIxB)
            (nextOutputTokenIndex == successTokenIndex)
          else bool
            (let !r' = r in goUnknown failureState (ix + 1) (outputSz + 1) failureTokenIndex ix (r' : output) tokenIxB)
            (goUnknown failureState (ix + 1) outputSz failureTokenIndex nextOutputStart output tokenIxB)
            (nextOutputTokenIndex == failureTokenIndex)
      TransitionCompactDfstMultiple theMap ->
        let MotionCompactDfst nextState outputIndex = DM.lookup tokenB theMap
         in bool
              (let !r' = r in goUnknown nextState (ix + 1) (outputSz + 1) outputIndex ix (r' : output) tokenIxB)
              (goUnknown nextState (ix + 1) outputSz outputIndex nextOutputStart output tokenIxB)
              (nextOutputTokenIndex == outputIndex)
    where
    {-# INLINE r #-}
    r = Ranged nextOutputStart (ix - nextOutputStart) (PM.indexArray outputs nextOutputTokenIndex)


evaluateAscii :: forall m.
     CompactDfst Char m
  -> Bytes
  -> Either AsciiException (Maybe (Array (Ranged m)))
evaluateAscii (CompactDfst transitions finals outputs) (Bytes tokens s0 len0) =
  if s0 >= end
    then Right $! bool Nothing (Just mempty) (SU.member 0 finals)
    else case B.indexAscii tokens s0 of
      Left err -> Left err
      Right token0 -> case PM.indexArray transitions 0 of
        TransitionCompactDfstSingle (CompactSequence string successState failureState successToken failureToken) ->
          if PM.indexPrimArray string 0 == token0
            -- Sequences are guaranteed to have length >= 1, so this indexing does
            -- not need to be guarded.
            then goSequence (unPrimArray string) (unInt 1) (unInt (PM.sizeofPrimArray string)) (unInt successState) (unInt failureState) (unInt failureToken) (unInt 1) (unInt 0) (unInt successToken) (unInt 0) [] (unInt (s0 + 1))
            else goUnknown (unInt failureState) (unInt 1) (unInt 0) (unInt failureToken) (unInt 0) [] (unInt (s0 + 1))
        TransitionCompactDfstMultiple theMap ->
          let MotionCompactDfst nextState outputTokenIndex = DM.lookup token0 theMap
           in goUnknown (unInt nextState) (unInt 1) (unInt 0) (unInt outputTokenIndex) (unInt 0) [] (unInt (s0 + 1))
  where
  -- Implementation Note: Unfortunately, worker-wrapper misses its
  -- chance to unbox the arguments of goSequence. So, we must do
  -- it by hand instead.
  !end = s0 + len0
  goSequence :: ByteArray# -> Int# -> Int# -> Int# -> Int# -> Int# -> Int# -> Int# -> Int# -> Int# -> [Ranged m] -> Int# -> Either AsciiException (Maybe (Array (Ranged m)))
  goSequence !string !stringIx !stringSz !successState !failureState !failureTokenIndex !ix !outputSz !nextOutputTokenIndex !nextOutputStart !output !tokenIxA = if I# tokenIxA >= end
    then if I# stringIx < I# stringSz
      -- Sequences may not contain final states, so mid-sequence input
      -- termination always indicates an unrecognized input.
      then Right Nothing
      else if SU.member (I# successState) finals
        then let !r' = r in Right $! Just $! C.unsafeFromListReverseN (I# outputSz + 1) (r' : output)
        else Right Nothing
    else case B.indexAscii tokens (I# tokenIxA) of
      Left err -> Left err
      Right tokenB -> if I# stringIx < I# stringSz
        then if PM.indexPrimArray (PrimArray string :: PrimArray Char) (I# stringIx) == tokenB
          then goSequence string (unInt (I# stringIx + 1)) stringSz successState failureState failureTokenIndex (unInt (I# ix + 1)) outputSz nextOutputTokenIndex nextOutputStart output (unInt (I# tokenIxA + 1))
          else bool
            (let !r' = r in goUnknown failureState (unInt (I# ix + 1)) (unInt (I# outputSz + 1)) failureTokenIndex ix (r' : output) (unInt (I# tokenIxA + 1)))
            (goUnknown failureState (unInt (I# ix + 1)) outputSz failureTokenIndex nextOutputStart output (unInt (I# tokenIxA + 1)))
            ((I# nextOutputTokenIndex) == (I# failureTokenIndex))
        else goUnknown successState ix outputSz nextOutputTokenIndex nextOutputStart output tokenIxA
    where
    {-# INLINE r #-}
    r = Ranged (I# nextOutputStart) (I# ix - I# nextOutputStart) (PM.indexArray outputs (I# nextOutputTokenIndex))
  goUnknown :: Int# -> Int# -> Int# -> Int# -> Int# -> [Ranged m] -> Int# -> Either AsciiException (Maybe (Array (Ranged m)))
  goUnknown !state !ix !outputSz !nextOutputTokenIndex !nextOutputStart !output !tokenIxA = if I# tokenIxA >= end
    then if SU.member (I# state) finals
      then let !r' = r in Right $! Just $! C.unsafeFromListReverseN (I# outputSz + 1) (r' : output)
      else Right Nothing
    else case B.indexAscii tokens (I# tokenIxA) of
      Left err -> Left err
      Right tokenB -> case PM.indexArray transitions (I# state) of
        TransitionCompactDfstSingle (CompactSequence string successState failureState successTokenIndex failureTokenIndex) ->
          if PM.indexPrimArray string 0 == tokenB
            -- Sequences are guaranteed to have length >= 1, so this indexing does
            -- not need to be guarded.
            then bool
              (let !r' = r in goSequence (unPrimArray string) (unInt 1) (unInt (PM.sizeofPrimArray string)) (unInt successState) (unInt failureState) (unInt failureTokenIndex) (unInt (I# ix + 1)) (unInt (I# outputSz + 1)) (unInt successTokenIndex) ix (r' : output) (unInt (I# tokenIxA + 1)))
              (goSequence (unPrimArray string) (unInt 1) (unInt (PM.sizeofPrimArray string)) (unInt successState) (unInt failureState) (unInt failureTokenIndex) (unInt (I# ix + 1)) outputSz (unInt successTokenIndex) nextOutputStart output (unInt (I# tokenIxA + 1)))
              (I# nextOutputTokenIndex == successTokenIndex)
            else bool
              (let !r' = r in goUnknown (unInt failureState) (unInt (I# ix + 1)) (unInt (I# outputSz + 1)) (unInt failureTokenIndex) ix (r' : output) (unInt (I# tokenIxA + 1)))
              (goUnknown (unInt failureState) (unInt (I# ix + 1)) outputSz (unInt failureTokenIndex) nextOutputStart output (unInt (I# tokenIxA + 1)))
              (I# nextOutputTokenIndex == failureTokenIndex)
        TransitionCompactDfstMultiple theMap ->
          let !(MotionCompactDfst !nextState !outputIndex) = DM.lookup tokenB theMap
           in bool
                (let !r' = r in goUnknown (unInt nextState) (unInt (I# ix + 1)) (unInt (I# outputSz + 1)) (unInt outputIndex) ix (r' : output) (unInt (I# tokenIxA + 1)))
                (goUnknown (unInt nextState) (unInt (I# ix + 1)) outputSz (unInt outputIndex) nextOutputStart output (unInt (I# tokenIxA + 1)))
                (I# nextOutputTokenIndex == outputIndex)
    where
    {-# INLINE r #-}
    r = Ranged (I# nextOutputStart) (I# ix - I# nextOutputStart) (PM.indexArray outputs (I# nextOutputTokenIndex))

unInt :: Int -> Int#
{-# inline unInt #-}
unInt (I# i) = i

unPrimArray :: PrimArray Char -> ByteArray#
unPrimArray (PrimArray b) = b
