{-# language BangPatterns #-}

module Main (main) where

import Automata.Dfsa (Dfsa)
import Data.Char (toUpper)
import Data.Enum.Types (D(..))
import Data.Primitive (PrimArray)
import Gauge (bgroup,bench,defaultMain,whnf,nf)

import qualified Alphabet as A
import qualified Automata.Dfsa as Dfsa
import qualified Automata.Dfsa.Unboxed as UnboxedDfsa
import qualified Data.Bytes as Bytes
import qualified GHC.Exts as E


main :: IO ()
main = defaultMain
  [ bgroup "Dfsa"
    [ bgroup "evaluate"
      [ bgroup "alphabet"
        [ bgroup "once"
          [ bench "lifted" (whnf (\x -> Dfsa.evaluatePrimArray x A.once) A.liftedAcceptor)
          , bench "optimal" (whnf (\x -> A.evaluateOptimally x) A.once)
          , bench "unboxed" (whnf (\x -> UnboxedDfsa.evaluatePrimArray x A.once) A.unboxedAcceptor)
          ]
        , bgroup "twice"
          [ bench "lifted" (whnf (\x -> Dfsa.evaluatePrimArray x A.twice) A.liftedAcceptor)
          , bench "optimal" (whnf (\x -> A.evaluateOptimally x) A.twice)
          , bgroup "unboxed"
            [ bench "utf32" (whnf (\x -> UnboxedDfsa.evaluatePrimArray x A.twice) A.unboxedAcceptor)
            , bench "ascii" (whnf (\x -> UnboxedDfsa.evaluateAscii x (Bytes.fromPrimArray A.twiceAscii)) A.unboxedAcceptor)
            , bench "utf8" (whnf (\x -> UnboxedDfsa.evaluateUtf8 x (Bytes.fromPrimArray A.twiceAscii)) A.unboxedAcceptor)
            ]
          ]
        ]
      ]
    , bgroup "union"
      [ bgroup "identical"
        [ bench "10" (whnf (\x -> Dfsa.union x x) dfsa1_10)
        , bench "20" (whnf (\x -> Dfsa.union x x) dfsa1_20)
        , bench "40" (whnf (\x -> Dfsa.union x x) dfsa1_40)
        , bench "80" (whnf (\x -> Dfsa.union x x) dfsa1_80)
        , bench "160" (whnf (\x -> Dfsa.union x x) dfsa1_160)
        , bench "320" (whnf (\x -> Dfsa.union x x) dfsa1_320)
        ]
      , bgroup "disjoint-start"
        [ bench "10" (whnf (\x -> Dfsa.union dfsa2_10 x) dfsa1_10)
        , bench "20" (whnf (\x -> Dfsa.union dfsa2_20 x) dfsa1_20)
        ]
      , bgroup "disjoint-end"
        [ bench "5" (whnf (\x -> Dfsa.union dfsa3_5 x) dfsa1_5)
        , bench "10" (whnf (\x -> Dfsa.union dfsa3_10 x) dfsa1_10)
        , bench "20" (whnf (\x -> Dfsa.union dfsa3_20 x) dfsa1_20)
        , bench "40" (whnf (\x -> Dfsa.union dfsa3_40 x) dfsa1_40)
        , bench "80" (whnf (\x -> Dfsa.union dfsa3_80 x) dfsa1_80)
        , bench "160" (whnf (\x -> Dfsa.union dfsa3_160 x) dfsa1_160)
        , bench "320" (whnf (\x -> Dfsa.union dfsa3_320 x) dfsa1_320)
        , bench "640" (whnf (\x -> Dfsa.union dfsa3_640 x) dfsa1_640)
        ]
      , bgroup "disjoint-throughout"
        [ bench "10" (whnf (\x -> Dfsa.union dfsa4_10 x) dfsa1_10)
        , bench "20" (whnf (\x -> Dfsa.union dfsa4_20 x) dfsa1_20)
        ]
      , bgroup "disjoint-borders"
        [ bench "10" (whnf (\x -> Dfsa.union dfsa5_10 x) dfsa1_10)
        , bench "20" (whnf (\x -> Dfsa.union dfsa5_20 x) dfsa1_20)
        ]
      ]
    ]
  ]

dfsa1_5 :: Dfsa D
dfsa1_5 = Dfsa.buildDefaulted (dfsaBuilder1 5)

dfsa1_10 :: Dfsa D
dfsa1_10 = Dfsa.buildDefaulted (dfsaBuilder1 10)

dfsa1_20 :: Dfsa D
dfsa1_20 = Dfsa.buildDefaulted (dfsaBuilder1 20)

dfsa1_40 :: Dfsa D
dfsa1_40 = Dfsa.buildDefaulted (dfsaBuilder1 40)

dfsa1_80 :: Dfsa D
dfsa1_80 = Dfsa.buildDefaulted (dfsaBuilder1 80)

dfsa1_160 :: Dfsa D
dfsa1_160 = Dfsa.buildDefaulted (dfsaBuilder1 160)

dfsa1_320 :: Dfsa D
dfsa1_320 = Dfsa.buildDefaulted (dfsaBuilder1 320)

dfsa1_640 :: Dfsa D
dfsa1_640 = Dfsa.buildDefaulted (dfsaBuilder1 640)

dfsa2_10 :: Dfsa D
dfsa2_10 = Dfsa.buildDefaulted (dfsaBuilder2 10)

dfsa2_20 :: Dfsa D
dfsa2_20 = Dfsa.buildDefaulted (dfsaBuilder2 20)

dfsa3_5 :: Dfsa D
dfsa3_5 = Dfsa.buildDefaulted (dfsaBuilder3 5)

dfsa3_10 :: Dfsa D
dfsa3_10 = Dfsa.buildDefaulted (dfsaBuilder3 10)

dfsa3_20 :: Dfsa D
dfsa3_20 = Dfsa.buildDefaulted (dfsaBuilder3 20)

dfsa3_40 :: Dfsa D
dfsa3_40 = Dfsa.buildDefaulted (dfsaBuilder3 40)

dfsa3_80 :: Dfsa D
dfsa3_80 = Dfsa.buildDefaulted (dfsaBuilder3 80)

dfsa3_160 :: Dfsa D
dfsa3_160 = Dfsa.buildDefaulted (dfsaBuilder3 160)

dfsa3_320 :: Dfsa D
dfsa3_320 = Dfsa.buildDefaulted (dfsaBuilder3 320)

dfsa3_640 :: Dfsa D
dfsa3_640 = Dfsa.buildDefaulted (dfsaBuilder3 640)

dfsa4_10 :: Dfsa D
dfsa4_10 = Dfsa.buildDefaulted (dfsaBuilder4 10)

dfsa4_20 :: Dfsa D
dfsa4_20 = Dfsa.buildDefaulted (dfsaBuilder4 20)

dfsa5_10 :: Dfsa D
dfsa5_10 = Dfsa.buildDefaulted (dfsaBuilder5 10)

dfsa5_20 :: Dfsa D
dfsa5_20 = Dfsa.buildDefaulted (dfsaBuilder5 20)

-- The DFSA given by:
--
-- 00 --D1-> 01 --D1-> .. --D1-> ZX --D1-> ZY
--  |         |                   |         |
--  +---------+------> ZZ <-------+---------+
--
-- On D1 anywhere, we transition to the state corresponding
-- to the current state's numeric successor. All non-D1 input
-- leads to state ZZ, which is intuitively understood to be
-- the failure state. State ZY is the only final state.
dfsaBuilder1 :: Int -> Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder1 sz start _ = do
  let go !ix !old = if ix < sz
        then do
          new <- Dfsa.state
          Dfsa.transition D1 D1 old new
          go (ix + 1) new
        else Dfsa.accept old
  go (1 :: Int) start

-- The DFSA given by:
--
-- 00 --D2-> 01 --D1-> .. --D1-> 98 --D1-> 99
--  |         |                   |         |
--  +---------+------> 100 <----------------+
--
-- This is the same as dfsaBuilder1 except that the transition
-- from 00 to 01 requires D2.
dfsaBuilder2 :: Int -> Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder2 sz start _ = do
  let go !ix !old = if ix < sz
        then do
          new <- Dfsa.state
          if ix == 1
            then Dfsa.transition D2 D2 old new
            else Dfsa.transition D1 D1 old new
          go (ix + 1) new
        else Dfsa.accept old
  go (1 :: Int) start

-- The DFSA given by:
--
-- 00 --D1-> 01 --D1-> .. --D1-> ZX --D2-> ZY
--  |         |                   |         |
--  +---------+------> ZZ <-----------------+
--
-- This is the same as dfsaBuilder1 except that the transition
-- from ZX to ZY requires D3.
dfsaBuilder3 :: Int -> Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder3 sz start _ = do
  let go !ix !old = if ix < sz
        then do
          new <- Dfsa.state
          if ix == sz - 1
            then Dfsa.transition D3 D3 old new
            else Dfsa.transition D1 D1 old new
          go (ix + 1) new
        else Dfsa.accept old
  go (1 :: Int) start

-- The DFSA given by:
--
-- 00 --D2-> 01 --D2-> .. --D2-> ZX --D2-> ZY
--  |         |                   |         |
--  +---------+------> ZZ <-----------------+
--
-- This is the same as dfsaBuilder1 except that all the transitions
-- require D2 instead of D1.
dfsaBuilder4 :: Int -> Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder4 sz start _ = do
  let go !ix !old = if ix < sz
        then do
          new <- Dfsa.state
          Dfsa.transition D2 D2 old new
          go (ix + 1) new
        else Dfsa.accept old
  go (1 :: Int) start

-- The DFSA given by:
--
-- 00 --D3-> 01 --D1-> .. --D1-> ZX --D2-> ZY
--  |         |                   |         |
--  +---------+------> ZZ <-----------------+
--
-- This is the same as dfsaBuilder1 except that the transition
-- from ZX to ZY requires D2 and the transition from 00 to 01
-- requires D3.
dfsaBuilder5 :: Int -> Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder5 sz start _ = do
  let go !ix !old = if ix < sz
        then do
          new <- Dfsa.state
          if ix == 1
            then Dfsa.transition D3 D3 old new
            else if ix == sz - 1
              then Dfsa.transition D2 D2 old new
              else Dfsa.transition D1 D1 old new
          go (ix + 1) new
        else Dfsa.accept old
  go (1 :: Int) start

