{-# language BangPatterns #-}

module Sentence
  ( Tag(..)
  , liftedTransducer
  , compactTransducer
  , compactUnboxedTransducer
  , fastCat
  , fastCatAscii
  , slowDog
  , fastCatExpected
  , slowDogExpected
  ) where

import Automata.Dfst (Dfst)
import Automata.Dfst.Compact (CompactDfst)
import Control.DeepSeq (NFData(..))
import Data.Primitive (ByteArray)
import Data.Char (ord)
import qualified Automata.Dfst as Dfst
import qualified Automata.Dfst.Compact as CDfst
import qualified Automata.Dfst.Compact.Unboxed as CUDfst
import qualified GHC.Exts as E

data Tag
  = Dog
  | Cat
  | Fast
  | Slow
  | None
  deriving (Eq,Ord,Bounded,Show)

instance NFData Tag where
  rnf !_ = ()

instance Semigroup Tag where
  (<>) = min
instance Monoid Tag where
  mempty = maxBound

fastCat :: String
fastCat = "The cat ran home"

fastCatAscii :: ByteArray
fastCatAscii = E.fromList (map (fromIntegral . ord) fastCat)

slowDog :: String
slowDog = "The dog walked home"

fastCatExpected :: [Tag]
fastCatExpected =
  [ None
  , None
  , None
  , None
  , Cat
  , Cat
  , Cat
  , None
  , Fast
  , Fast
  , Fast
  , None
  , None
  , None
  , None
  , None
  ]

slowDogExpected :: [Tag]
slowDogExpected =
  [ None
  , None
  , None
  , None
  , Dog
  , Dog
  , Dog
  , None
  , Slow
  , Slow
  , Slow
  , Slow
  , Slow
  , Slow
  , None
  , None
  , None
  , None
  , None
  ]

compactTransducer :: CompactDfst Char Tag
compactTransducer = CDfst.compact liftedTransducer

compactUnboxedTransducer :: CUDfst.CompactDfst Char Tag
compactUnboxedTransducer = CUDfst.fromLifted compactTransducer

liftedTransducer :: Dfst Char Tag
liftedTransducer = Dfst.buildDefaulted $ \s0 _ -> do
  s1 <- Dfst.state
  s2 <- Dfst.state
  s3 <- Dfst.state
  s4 <- Dfst.state
  s5 <- Dfst.state
  s6 <- Dfst.state
  s7 <- Dfst.state
  s8 <- Dfst.state
  s9 <- Dfst.state
  s10 <- Dfst.state
  s11 <- Dfst.state
  s12 <- Dfst.state
  s13 <- Dfst.state
  s14 <- Dfst.state
  s15 <- Dfst.state
  s16 <- Dfst.state
  s17 <- Dfst.state
  s18 <- Dfst.state
  s19 <- Dfst.state
  s5x <- Dfst.state
  s6x <- Dfst.state
  s9x <- Dfst.state
  s10x <- Dfst.state
  Dfst.transition 'T' 'T' None s0 s1
  Dfst.transition 'h' 'h' None s1 s2
  Dfst.transition 'e' 'e' None s2 s3
  Dfst.transition ' ' ' ' None s3 s4
  Dfst.transition 'd' 'd' Dog s4 s5
  Dfst.transition 'o' 'o' Dog s5 s6
  Dfst.transition 'g' 'g' Dog s6 s7
  Dfst.transition 'c' 'c' Cat s4 s5x
  Dfst.transition 'a' 'a' Cat s5x s6x
  Dfst.transition 't' 't' Cat s6x s7
  Dfst.transition ' ' ' ' None s7 s8
  Dfst.transition 'w' 'w' Slow s8 s9
  Dfst.transition 'a' 'a' Slow s9 s10
  Dfst.transition 'l' 'l' Slow s10 s11
  Dfst.transition 'k' 'k' Slow s11 s12
  Dfst.transition 'e' 'e' Slow s12 s13
  Dfst.transition 'd' 'd' Slow s13 s14
  Dfst.transition 'r' 'r' Fast s8 s9x
  Dfst.transition 'a' 'a' Fast s9x s10x
  Dfst.transition 'n' 'n' Fast s10x s14
  Dfst.transition ' ' ' ' None s14 s15
  Dfst.transition 'h' 'h' None s15 s16
  Dfst.transition 'o' 'o' None s16 s17
  Dfst.transition 'm' 'm' None s17 s18
  Dfst.transition 'e' 'e' None s18 s19
  Dfst.accept s19

