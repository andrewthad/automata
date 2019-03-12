{-# language BangPatterns #-}

module Main (main) where

import Data.Enum.Types (D(..))
import Gauge
import Automata.Dfsa (Dfsa)
import qualified Automata.Dfsa as Dfsa

main :: IO ()
main = defaultMain
  [ bgroup "Dfsa"
    [ bgroup "union"
      [ bench "identical" (whnf (\x -> Dfsa.union x x) dfsa1) 
      , bench "disjoint-start" (whnf (\x -> Dfsa.union dfsa2 x) dfsa1)
      , bench "disjoint-end" (whnf (\x -> Dfsa.union dfsa3 x) dfsa1)
      , bench "disjoint-throughout" (whnf (\x -> Dfsa.union dfsa4 x) dfsa1)
      ]
    ]
  ]

dfsa1 :: Dfsa D
dfsa1 = Dfsa.buildDefaulted dfsaBuilder1

dfsa2 :: Dfsa D
dfsa2 = Dfsa.buildDefaulted dfsaBuilder2

dfsa3 :: Dfsa D
dfsa3 = Dfsa.buildDefaulted dfsaBuilder3

dfsa4 :: Dfsa D
dfsa4 = Dfsa.buildDefaulted dfsaBuilder4

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
dfsaBuilder1 :: Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder1 start _ = do
  let go !ix !old = if ix < dfsaStateCount
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
dfsaBuilder2 :: Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder2 start _ = do
  let go !ix !old = if ix < dfsaStateCount
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
-- from ZX to ZY requires D2.
dfsaBuilder3 :: Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder3 start _ = do
  let go !ix !old = if ix < dfsaStateCount
        then do
          new <- Dfsa.state
          if ix == dfsaStateCount - 1
            then Dfsa.transition D2 D2 old new
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
dfsaBuilder4 :: Dfsa.State s -> Dfsa.State s -> Dfsa.Builder D s ()
dfsaBuilder4 start _ = do
  let go !ix !old = if ix < dfsaStateCount
        then do
          new <- Dfsa.state
          Dfsa.transition D2 D2 old new
          go (ix + 1) new
        else Dfsa.accept old
  go (1 :: Int) start

dfsaStateCount :: Int
dfsaStateCount = 20
