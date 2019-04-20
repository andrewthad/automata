{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DataKinds #-}
{-# language DeriveFunctor #-}
{-# language DuplicateRecordFields #-}
{-# language GADTs #-}
{-# language KindSignatures #-}
{-# language MagicHash #-}
{-# language MultiWayIf #-}
{-# language StandaloneDeriving #-}

module Data.Bytes
  ( Bytes(..)
  , Utf8State(..)
  , Utf8Exception(..)
  , Utf8Sequence(..)
  , Utf8EndOfInput(..)
  , AsciiException(..)
    -- * Folds
  , foldl'
  , foldlM'
  , foldlAscii'
  , foldlUtf8'
    -- * Conversion
  , fromByteArray
  , fromPrimArray
  ) where

import Data.Bifunctor (first)
import Control.Exception (Exception)
import Control.Monad (when)
import Data.Word (Word8)
import Data.Bits (unsafeShiftL,xor,(.&.),(.|.))
import Data.Functor (($>))
import Data.Primitive (PrimArray(..),ByteArray(..))
import Data.Kind (Type)
import GHC.Base (unsafeChr)
import GHC.Exts (Word(W#),Char(C#),chr#,word2Int#)
import qualified Data.Primitive as PM

data Bytes = Bytes
  !(PrimArray Word8)
  !Int
  !Int

-- | Exception encountered while attempting to interpret a series
-- of bytes as ASCII-encoded text.
data AsciiException = AsciiException
  { position :: !Int
  , byte :: !Word8
  } deriving (Show,Eq)

instance Exception AsciiException

data Utf8Exception
  = Utf8ExceptionSequence !Utf8SequenceException
    -- ^ Encountered a bad byte sequence.
  | Utf8ExceptionEndOfInput !(Utf8EndOfInput 'Done ())
    -- ^ Input ended when more characters more expected.
  deriving (Show,Eq)

data Utf8State a
  = Utf8StateSequence !Utf8SequenceException
  | Utf8StateEndOfInput !(Utf8EndOfInput 'More a)
  deriving (Show,Eq,Functor)

data Utf8SequenceException = Utf8SequenceException
  { position :: !Int
  , context :: !Utf8Sequence
  } deriving (Show,Eq)

-- | Each of these data constructors contains the bytes
-- that comprise the invalid sequence. The @position@ in
-- the 'Utf8SequenceException that this invalid sequence is a part
-- of refers to the index of the invalid byte, not the leading byte
-- in the sequence. This feels a little usual, but when decoding
-- chunked input, the leading byte may not even belong to the
-- chunk in which decoding failed. If we used the index of the leading
-- byte instead, we would need to report a negative index in these
-- situations. To avoid ever needing to do this, we use the index
-- of the bad byte instead. This means that the reported will always
-- be a valid into the bytes.a
--
-- Keep in mind that the number at the end of the data constructor
-- refers to the number of bytes that were inspected, not the number
-- of bytes expected in the sequence that failed.
data Utf8Sequence
  = Utf8Sequence1 !Word8
  | Utf8Sequence2 !Word8 !Word8
  | Utf8Sequence3 !Word8 !Word8 !Word8
  | Utf8Sequence4 !Word8 !Word8 !Word8 !Word8
  deriving (Show,Eq)

data IndexChar = IndexChar !Int !Char

data Continuation = More | Done

-- | Type constructor arguments are the value type and the 
data Utf8EndOfInput :: Continuation -> Type -> Type where
  Utf8EndOfInput0 :: !a -> Utf8EndOfInput 'More a
  Utf8EndOfInput1 :: !Word8 -> !a -> Utf8EndOfInput c a
  Utf8EndOfInput2 :: !Word8 -> !Word8 -> !a -> Utf8EndOfInput c a
  Utf8EndOfInput3 :: !Word8 -> !Word8 -> !Word8 -> !a -> Utf8EndOfInput c a

deriving instance Functor (Utf8EndOfInput c)
deriving instance Eq a => Eq (Utf8EndOfInput c a)
deriving instance Show a => Show (Utf8EndOfInput c a)

fromByteArray :: ByteArray -> Bytes
fromByteArray x@(ByteArray y) = Bytes (PrimArray y) 0 (PM.sizeofByteArray x)

fromPrimArray :: PrimArray Word8 -> Bytes
fromPrimArray !x = Bytes x 0 (PM.sizeofPrimArray x)

-- | Strict left to right fold.
foldl' :: (b -> Word8 -> b) -> b -> Bytes -> b
{-# INLINE foldl' #-}
foldl' f z (Bytes arr s l) = go z s
  where
  !end = s + l
  -- tail recursive; traverses array left to right
  go !acc !i
    | i < end = let !x = PM.indexPrimArray arr i in go (f acc x) (i + 1)
    | otherwise = acc

-- | Strict left-associated fold over bytes.
{-# INLINE foldlM' #-}
foldlM' :: Monad m => (b -> Word8 -> m b) -> b -> Bytes -> m b
foldlM' f z0 (Bytes arr s l) = go s z0
  where
    !end = s + l
    go !i !acc1
      | i < end = do
          let !x = PM.indexPrimArray arr i
          acc2 <- f acc1 x
          go (i + 1) acc2
      | otherwise = return acc1

-- | Strict left-associated fold over characters when the
--   bytes are interpreted as ASCII-encoded text. If a byte
--   above @0x7F@ is encountered, this returns 'Left' with
--   the position of the invalid byte.
foldlAscii' :: (b -> Char -> b) -> b -> Bytes -> Either AsciiException b
{-# INLINE foldlAscii' #-}
foldlAscii' f z0 (Bytes arr s l) = go s z0
  where
    !end = s + l
    go !i !acc1
      | i < end = do
          let !x = PM.indexPrimArray arr i
          if x < 128
            then go (i + 1) (f acc1 (word8ToChar x))
            else Left (AsciiException i x)
      | otherwise = return acc1

word8ToChar :: Word8 -> Char
word8ToChar = unsafeChr . fromIntegral

-- | Strict left-associated fold over bytes.
foldlUtf8' :: 
     (b -> Char -> b)
  -> b
  -> Bytes
  -> Utf8State b
{-# INLINE foldlUtf8' #-}
foldlUtf8' f z0 (Bytes arr s l) = go s z0
  where
  !end = s + l
  go !i !acc1
    | i < end - 3 = case unsafeAdvanceChar4 arr i of
        Left e -> Utf8StateSequence e
        Right (IndexChar pos c) -> go pos (f acc1 c)
    | i == end - 3 = case unsafeAdvanceChar3 arr i of
        Left e -> e $> acc1
        Right (IndexChar pos c) -> go pos (f acc1 c)
    | i == end - 2 = case unsafeAdvanceChar2 arr i of
        Left e -> e $> acc1
        Right (IndexChar pos c) -> go pos (f acc1 c)
    | i == end - 1 = case unsafeAdvanceChar1 arr i of
        Left e -> e $> acc1
        Right (IndexChar pos c) -> go pos (f acc1 c)
    | otherwise = Utf8StateEndOfInput (Utf8EndOfInput0 acc1)

-- Internal function. Precondition: there is exactly one byte
-- remaining in the slice of bytes.
unsafeAdvanceChar1 :: PrimArray Word8 -> Int -> Either (Utf8State ()) IndexChar
{-# INLINE unsafeAdvanceChar1 #-}
unsafeAdvanceChar1 !arr !ix
  | oneByteChar firstByte = Right (IndexChar (ix + 1) (unsafeWordToChar (word8ToWord firstByte)))
  | twoByteChar firstByte || threeByteChar firstByte || fourByteChar firstByte =
      Left $ Utf8StateEndOfInput $ Utf8EndOfInput1 firstByte ()
  | otherwise = Left $ Utf8StateSequence $ Utf8SequenceException
      { position = ix
      , context = Utf8Sequence1 firstByte
      }
  where
  firstByte :: Word8
  !firstByte = PM.indexPrimArray arr ix

-- Internal function. Precondition: there are exactly two bytes
-- remaining in the slice of bytes.
unsafeAdvanceChar2 :: PrimArray Word8 -> Int -> Either (Utf8State ()) IndexChar
{-# INLINE unsafeAdvanceChar2 #-}
unsafeAdvanceChar2 !arr !ix
  | oneByteChar firstByte = Right (IndexChar (ix + 1) (unsafeWordToChar (word8ToWord firstByte)))
  | twoByteChar firstByte = first Utf8StateSequence (handleTwoByteChar arr ix firstByte)
  | threeByteChar firstByte || fourByteChar firstByte = do
      let !secondByte = PM.indexPrimArray arr (ix + 1)
      when (not (followingByte secondByte)) $ do
        Left $ Utf8StateSequence $ Utf8SequenceException
          { position = ix + 1
          , context = Utf8Sequence2 firstByte secondByte
          }
      Left $ Utf8StateEndOfInput $ Utf8EndOfInput2 firstByte secondByte ()
  | otherwise = Left $ Utf8StateSequence $ Utf8SequenceException
      { position = ix
      , context = Utf8Sequence1 firstByte
      }
  where
  firstByte :: Word8
  !firstByte = PM.indexPrimArray arr ix

-- Internal function. Precondition: there are exactly three bytes
-- remaining in the slice of bytes.
unsafeAdvanceChar3 :: PrimArray Word8 -> Int -> Either (Utf8State ()) IndexChar
{-# INLINE unsafeAdvanceChar3 #-}
unsafeAdvanceChar3 !arr !ix
  | oneByteChar firstByte = Right (IndexChar (ix + 1) (unsafeWordToChar (word8ToWord firstByte)))
  | twoByteChar firstByte = first Utf8StateSequence (handleTwoByteChar arr ix firstByte)
  | threeByteChar firstByte = first Utf8StateSequence (handleThreeByteChar arr ix firstByte)
  | fourByteChar firstByte = do
      let !secondByte = PM.indexPrimArray arr (ix + 1)
      when (not (followingByte secondByte)) $ do
        Left $ Utf8StateSequence $ Utf8SequenceException
          { position = ix + 1
          , context = Utf8Sequence2 firstByte secondByte
          }
      let !thirdByte = PM.indexPrimArray arr (ix + 2)
      when (not (followingByte thirdByte)) $ do
        Left $ Utf8StateSequence $ Utf8SequenceException
          { position = ix + 2
          , context = Utf8Sequence3 firstByte secondByte thirdByte
          }
      Left $ Utf8StateEndOfInput $ Utf8EndOfInput3 firstByte secondByte thirdByte ()
  | otherwise = Left $ Utf8StateSequence $ Utf8SequenceException
      { position = ix
      , context = Utf8Sequence1 firstByte
      }
  where
  firstByte :: Word8
  !firstByte = PM.indexPrimArray arr ix

-- Internal function. Precondition: there are at least four bytes
-- remaining in the ByteArray. That is: end - ix >= 4
unsafeAdvanceChar4 :: PrimArray Word8 -> Int -> Either Utf8SequenceException IndexChar
{-# INLINE unsafeAdvanceChar4 #-}
unsafeAdvanceChar4 !arr !ix
  | oneByteChar firstByte =
      Right (IndexChar (ix + 1) (unsafeWordToChar (word8ToWord firstByte)))
  | twoByteChar firstByte = handleTwoByteChar arr ix firstByte
  | threeByteChar firstByte = handleThreeByteChar arr ix firstByte
  | fourByteChar firstByte = do
      let !secondByte = PM.indexPrimArray arr (ix + 1)
      when (not (followingByte secondByte)) $ do
        Left $ Utf8SequenceException
          { position = ix + 1
          , context = Utf8Sequence2 firstByte secondByte
          }
      let !thirdByte = PM.indexPrimArray arr (ix + 2)
      when (not (followingByte thirdByte)) $ do
        Left $ Utf8SequenceException
          { position = ix + 2
          , context = Utf8Sequence3 firstByte secondByte thirdByte
          }
      let !fourthByte = PM.indexPrimArray arr (ix + 3)
      when (not (followingByte fourthByte)) $ do
        Left $ Utf8SequenceException
          { position = ix + 3
          , context = Utf8Sequence4 firstByte secondByte thirdByte fourthByte
          }
      Right $ IndexChar
        (ix + 4)
        (charFromFourBytes firstByte secondByte thirdByte fourthByte)
  | otherwise = Left $ Utf8SequenceException
      { position = ix
      , context = Utf8Sequence1 firstByte
      }
  where
  firstByte :: Word8
  !firstByte = PM.indexPrimArray arr ix

-- Does not do bounds checking.
handleThreeByteChar :: PrimArray Word8 -> Int -> Word8 -> Either Utf8SequenceException IndexChar
{-# INLINE handleThreeByteChar #-}
handleThreeByteChar !arr !ix !firstByte = do
  let !secondByte = PM.indexPrimArray arr (ix + 1)
  when (not (followingByte secondByte)) $ do
    Left $ Utf8SequenceException
      { position = ix + 1
      , context = Utf8Sequence2 firstByte secondByte
      }
  let !thirdByte = PM.indexPrimArray arr (ix + 2)
  when (not (followingByte thirdByte)) $ do
    Left $ Utf8SequenceException
      { position = ix + 2
      , context = Utf8Sequence3 firstByte secondByte thirdByte
      }
  Right $ IndexChar
    (ix + 3)
    (charFromThreeBytes firstByte secondByte thirdByte)

-- Does not do bounds checking.
handleTwoByteChar :: PrimArray Word8 -> Int -> Word8 -> Either Utf8SequenceException IndexChar
{-# INLINE handleTwoByteChar #-}
handleTwoByteChar !arr !ix !firstByte = do
  let !secondByte = PM.indexPrimArray arr (ix + 1)
  if | followingByte secondByte -> Right $ IndexChar
         (ix + 2)
         (charFromTwoBytes firstByte secondByte)
     | otherwise -> Left $ Utf8SequenceException
         { position = ix + 1
         , context = Utf8Sequence2 firstByte secondByte
         }


-- Why is this unsafe? It is because there are some values
-- the cannot be used for a Char
unsafeWordToChar :: Word -> Char
unsafeWordToChar (W# w) = C# (chr# (word2Int# w))

word8ToWord :: Word8 -> Word
word8ToWord = fromIntegral

-- Is this byte allowed to follow the leading byte in
-- an UTF-8 sequence. This is the same check for sequences
-- of length two, three, or four.
followingByte :: Word8 -> Bool
followingByte !w = xor w 0b01000000 .&. 0b11000000 == 0b11000000

oneByteChar :: Word8 -> Bool
oneByteChar !w = w .&. 0b10000000 == 0

twoByteChar :: Word8 -> Bool
twoByteChar w = w .&. 0b11100000 == 0b11000000

threeByteChar :: Word8 -> Bool
threeByteChar !w = w .&. 0b11110000 == 0b11100000

fourByteChar :: Word8 -> Bool
fourByteChar !w = w .&. 0b11111000 == 0b11110000

-- Precondition: The bytes are already known to be admissible.
-- The leading bits of the arguments must be: [w1: 110][w2: 10].
charFromTwoBytes :: Word8 -> Word8 -> Char
{-# INLINE charFromTwoBytes #-}
charFromTwoBytes w1 w2 = unsafeWordToChar $
  unsafeShiftL (word8ToWord w1 .&. 0b00011111) 6 .|. 
  (word8ToWord w2 .&. 0b00111111)

charFromThreeBytes :: Word8 -> Word8 -> Word8 -> Char
{-# INLINE charFromThreeBytes #-}
charFromThreeBytes w1 w2 w3 = unsafeWordToChar $
  unsafeShiftL (word8ToWord w1 .&. 0b00001111) 12 .|. 
  unsafeShiftL (word8ToWord w2 .&. 0b00111111) 6 .|. 
  (word8ToWord w3 .&. 0b00111111)

charFromFourBytes :: Word8 -> Word8 -> Word8 -> Word8 -> Char
{-# INLINE charFromFourBytes #-}
charFromFourBytes w1 w2 w3 w4 = unsafeWordToChar $
  unsafeShiftL (word8ToWord w1 .&. 0b00000111) 18 .|. 
  unsafeShiftL (word8ToWord w2 .&. 0b00111111) 12 .|. 
  unsafeShiftL (word8ToWord w3 .&. 0b00111111) 6 .|. 
  (word8ToWord w4 .&. 0b00111111)

