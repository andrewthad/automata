{-# language DerivingStrategies #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}

import Automata.Dfsa (Dfsa)
import Automata.Dfst (Dfst)
import Automata.Nfsa (Nfsa)
import Automata.Nfst (Nfst)
import Automata.Dfst.Compact (Ranged(..))
import Control.Monad (forM_,replicateM)
import Data.Enum.Types (A(..),B(..),C(..),D(..),E(..))
import Data.Monoid (All(..))
import Data.Primitive (Array)
import Data.Proxy (Proxy(..))
import Data.Set (Set)
import Test.HUnit ((@?=),assertBool)
import Test.LeanCheck (Listable,(\/),cons0)
import Test.LeanCheck.Instances.Enum ()
import Test.QuickCheck (Arbitrary)
import Test.QuickCheck.Instances.Enum ()
import Test.Tasty (TestTree,defaultMain,testGroup,adjustOption)
import Test.Tasty.HUnit (testCase)

import qualified Alphabet as A
import qualified Sentence as SEN
import qualified Automata.Nfsa as Nfsa
import qualified Automata.Nfst as Nfst
import qualified Automata.Dfsa as Dfsa
import qualified Automata.Dfsa.Unboxed as UnboxedDfsa
import qualified Automata.Dfst as Dfst
import qualified Automata.Dfst.Compact as CDfst
import qualified Automata.Dfst.Compact.Unboxed as CUDfst
import qualified Automata.Nfsa as B
import qualified Data.Bytes as Bytes
import qualified Data.Set as S
import qualified Data.List as L
import qualified GHC.Exts as E
import qualified Test.Tasty.LeanCheck as TL
import qualified Test.QuickCheck as QC
import qualified Test.Tasty.QuickCheck as TQC
import qualified Test.QuickCheck.Classes as QCC

main :: IO ()
main = defaultMain
  $ adjustOption (\_ -> TL.LeanCheckTests 5000)
  $ tests 

tests :: TestTree
tests = testGroup "Automata"
  [ testGroup "Nfsa"
    [ testGroup "evaluate"
      [ testCase "A" (Nfsa.evaluate ex1 [D3,D1] @?= False)
      , testCase "B" (Nfsa.evaluate ex1 [D0,D1,D3] @?= True)
      , testCase "C" (Nfsa.evaluate ex1 [D1,D3,D3] @?= True)
      , testCase "D" (Nfsa.evaluate ex1 [D0,D0,D0] @?= False)
      , testCase "E" (Nfsa.evaluate ex1 [D0,D0] @?= False)
      , testCase "F" (Nfsa.evaluate ex1 [D1] @?= True)
      , testCase "G" (Nfsa.evaluate ex1 [D1,D3] @?= True)
      , testCase "H" (Nfsa.evaluate ex2 [D3,D3,D0] @?= False)
      , testCase "I" (Nfsa.evaluate ex2 [D3,D3,D2] @?= True)
      , testCase "J" (Nfsa.evaluate ex3 [D1] @?= False)
      , testCase "K" (Nfsa.evaluate ex3 [D1,D3] @?= True)
      , testCase "L" (Nfsa.evaluate ex3 [D1,D3,D0] @?= False)
      , testCase "M" (Nfsa.evaluate ex3 [D1,D3,D0,D2,D3] @?= True)
      , testCase "N" (Nfsa.evaluate ex3 [D1,D3,D3] @?= True)
      ]
    , testGroup "append"
      [ testCase "A" (Nfsa.evaluate (Nfsa.append ex1 ex2) [D0,D1,D3,D3,D3,D2] @?= True)
      , testCase "B" (Nfsa.evaluate (Nfsa.append ex1 ex2) [D0,D0,D3,D0] @?= False)
      , testCase "C" (Nfsa.evaluate (Nfsa.append ex1 ex2) [D1,D3] @?= True)
      , testCase "D" (Nfsa.evaluate (Nfsa.append ex2 ex3) [D3,D3,D2,D1,D3,D3] @?= True)
      , testCase "E" (Nfsa.evaluate (Nfsa.append ex2 ex3) [D3,D3,D2] @?= False)
      ]
    , testGroup "union"
      [ testGroup "unit"
        [ testCase "A" (Nfsa.evaluate (Nfsa.union ex1 ex2) [D3,D1] @?= True)
        , testCase "B" (Nfsa.evaluate (Nfsa.union ex1 ex2) [D3,D3,D2] @?= True)
        , testCase "C" (Nfsa.evaluate (Nfsa.union ex1 ex2) [D0,D0,D0] @?= False)
        ]
      ]
    , testGroup "toDfsa"
      [ testGroup "unit"
        [ testCase "A" (Dfsa.evaluate (Nfsa.toDfsa ex1) [D0,D1,D3] @?= True)
        , testCase "B" (Dfsa.evaluate (Nfsa.toDfsa ex1) [D3,D1] @?= False)
        , testCase "C" (Dfsa.evaluate (Nfsa.toDfsa (Nfsa.append ex1 ex2)) [D0,D1,D3,D3,D3,D2] @?= True)
        , testCase "D" (Dfsa.evaluate (Nfsa.toDfsa (Nfsa.append ex2 ex3)) [D3,D3,D2,D1,D3,D3] @?= True)
        , testCase "E" (Dfsa.evaluate (Nfsa.toDfsa (Nfsa.append ex1 ex2)) [D0,D0,D3,D0] @?= False)
        , testCase "F" (Nfsa.toDfsa ex1 == Nfsa.toDfsa ex4 @?= True)
        , testCase "G" (Nfsa.toDfsa ex1 == Nfsa.toDfsa ex2 @?= False)
        , testCase "H" (Nfsa.toDfsa ex5 == Nfsa.toDfsa ex6 @?= True)
        ]
      , testGroup "evaluation"
        [ TL.testProperty "1" $ \(a,b,c,d) -> Dfsa.evaluate (Nfsa.toDfsa ex1) [a,b,c,d] == Nfsa.evaluate ex1 [a,b,c,d]
        , TL.testProperty "2" $ \(a,b,c,d) -> Dfsa.evaluate (Nfsa.toDfsa ex2) [a,b,c,d] == Nfsa.evaluate ex2 [a,b,c,d]
        , TL.testProperty "3" $ \(a,b,c,d) -> Dfsa.evaluate (Nfsa.toDfsa ex3) [a,b,c,d] == Nfsa.evaluate ex3 [a,b,c,d]
        , TL.testProperty "4" $ \(a,b,c,d) -> Dfsa.evaluate (Nfsa.toDfsa ex4) [a,b,c,d] == Nfsa.evaluate ex4 [a,b,c,d]
        , TL.testProperty "5" $ \(a,b,c,d) -> Dfsa.evaluate (Nfsa.toDfsa ex5) [a,b,c,d] == Nfsa.evaluate ex5 [a,b,c,d]
        , TL.testProperty "6" $ \(a,b,c,d) -> Dfsa.evaluate (Nfsa.toDfsa ex6) [a,b,c,d] == Nfsa.evaluate ex6 [a,b,c,d]
        , TL.testProperty "7" $ \(a,b,c,d) -> Dfsa.evaluate (Nfsa.toDfsa ex7) [a,b,c,d] == Nfsa.evaluate ex7 [a,b,c,d]
        ]
      ]
    , lawsToTest (QCC.semiringLaws (Proxy :: Proxy (Nfsa D)))
    ]
  , testGroup "Dfsa"
    [ testGroup "builder"
      [ testCase "A" (exDfsa3 @?= exDfsa4)
      , testCase "B" (assertBool "" (exDfsa5 /= Dfsa.acceptance))
      ]
    , testGroup "evaluate"
      [ testCase "A" (Dfsa.evaluate exDfsa1 [D1] @?= True)
      , testCase "B" (Dfsa.evaluate exDfsa1 [D3,D2,D1,D2,D0] @?= True)
      , testCase "C" (Dfsa.evaluate exDfsa2 [D3,D3] @?= False)
      , testCase "D" (Dfsa.evaluate exDfsa2 [D1] @?= True)
      , testCase "E" (Dfsa.evaluate exDfsa2 [D0,D2] @?= True)
      , testCase "F" (Dfsa.evaluate exDfsa2 [D0,D2] @?= True)
      ]
    , testGroup "evaluatePrimArray"
      [ testGroup "alphabet"
        [ testGroup "once"
          [ testCase "lifted" (Dfsa.evaluatePrimArray A.liftedAcceptor A.once @?= True)
          , testCase "unboxed" (UnboxedDfsa.evaluatePrimArray A.unboxedAcceptor A.once @?= True)
          ]
        , testGroup "twice"
          [ testCase "lifted" (Dfsa.evaluatePrimArray A.liftedAcceptor A.twice @?= True)
          , testCase "optimal" (A.evaluateOptimally A.twice @?= True)
          , testGroup "unboxed"
            [ testCase "utf32" (UnboxedDfsa.evaluatePrimArray A.unboxedAcceptor A.twice @?= True)
            , testCase "ascii" (UnboxedDfsa.evaluateAscii A.unboxedAcceptor (Bytes.fromPrimArray A.twiceAscii) @?= Right True)
            , testCase "utf8" (UnboxedDfsa.evaluateUtf8 A.unboxedAcceptor (Bytes.fromPrimArray A.twiceAscii) @?= Right True)
            ]
          ]
        ]
      ]
    , testGroup "union"
      [ testGroup "unit"
        [ testCase "A" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [D0,D1,D3] @?= True)
        , testCase "B" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [D2,D3] @?= True)
        , testCase "C" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [D1,D3] @?= True)
        , testCase "D" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [D1,D3,D0] @?= False)
        , testCase "E" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [D1] @?= True)
        , testCase "F" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [D3] @?= False)
        , testCase "G" (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3) @?= Dfsa.union (Nfsa.toDfsa ex3) (Nfsa.toDfsa ex1))
        , testCase "H" (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex1) @?= (Nfsa.toDfsa ex1))
        , testCase "I" (Dfsa.union (Nfsa.toDfsa ex3) (Nfsa.toDfsa ex3) @?= (Nfsa.toDfsa ex3))
        ]
      , testGroup "idempotent"
        [ TL.testProperty "three" $ \x -> let y = mkLittleBinDfsa x in y == Dfsa.union y y
        , TL.testProperty "four" $ \x -> let y = mkBinDfsa x in y == Dfsa.union y y
        ]
      , testGroup "identity"
        [ TL.testProperty "left" $ \x -> let y = mkBinDfsa x in y == Dfsa.union Dfsa.rejection y
        , TL.testProperty "right" $ \x -> let y = mkBinDfsa x in y == Dfsa.union y Dfsa.rejection
        ]
      ]
    , testGroup "intersection"
      [ TL.testProperty "idempotent" $ \x -> let y = mkBinDfsa x in y == Dfsa.intersection y y
      , testGroup "identity"
        [ TL.testProperty "left" $ \x -> let y = mkBinDfsa x in y == Dfsa.intersection Dfsa.acceptance y
        , TL.testProperty "right" $ \x -> let y = mkBinDfsa x in y == Dfsa.intersection y Dfsa.acceptance
        ]
      ]
    , lawsToTest (QCC.semiringLaws (Proxy :: Proxy (Dfsa D)))
    ]
  , testGroup "Nfst"
    [ testGroup "evaluate"
      [ testCase "A" (Nfst.evaluate exNfst1 [D0,D1] @?= S.singleton [B1,B0])
      , testCase "B" (Nfst.evaluate exNfst1 [D2,D1,D3] @?= S.singleton [B1,B1,B1])
      , testCase "C" (Nfst.evaluate exNfst2 [D0,D0] @?= S.singleton [B0,B0])
      , testCase "D" (Nfst.evaluate exNfst2 [D1,D0] @?= S.fromList [[B0,B0],[B0,B1]])
      , testCase "E" (Nfst.evaluate exNfst3 [D0,D2] @?= S.singleton [B1,B0])
      , testCase "F" (Nfst.evaluate exNfst3 [D0,D1] @?= S.singleton [B0,B1])
      , testCase "G" (Nfst.evaluate (Nfst.union Nfst.rejection exNfst3) [D0,D1] @?= S.singleton [B0,B1])
      , testCase "H" (Nfst.evaluate (Nfst.union exNfst1 exNfst3) [D0,D1] @?= S.fromList [[B1,B0],[B0,B1]])
      , testCase "I" (Nfst.evaluate (Nfst.union exNfst3 exNfst1) [D0,D1] @?= S.fromList [[B1,B0],[B0,B1]])
      ]
    , testGroup "toDfst"
      [ testGroup "unit"
        [ testCase "A" (let x = Dfst.evaluate (Nfst.toDfst exNfst4) [D0,D1] in assertBool (show x) (setSubresult [B1, B0] x))
        , testCase "B" (let x = Dfst.evaluate (Nfst.toDfst exNfst5) [D1,D2] in assertBool (show x) (setSubresult [B0, B1] x))
        ]
      , testGroup "evaluation"
        [ TL.testProperty "4" $ \(input :: [D]) -> getAll (foldMap (\x -> All (subresult (L.reverse x) (Dfst.evaluate (Nfst.toDfst exNfst4) input))) (Nfst.evaluate exNfst4 input))
        , TL.testProperty "5" $ \(input :: [D]) -> getAll (foldMap (\x -> All (subresult (L.reverse x) (Dfst.evaluate (Nfst.toDfst exNfst5) input))) (Nfst.evaluate exNfst5 input))
        , TL.testProperty "6" $ \(input :: [D]) -> getAll (foldMap (\x -> All (subresult (L.reverse x) (Dfst.evaluate (Nfst.toDfst exNfst6) input))) (Nfst.evaluate exNfst6 input))
        ]
      ]
    ]
  , testGroup "Dfst"
    [ testGroup "evaluate"
      [ testCase "A" (Dfst.evaluate exDfst1 [D0,D2] @?= Nothing)
      , testCase "B" (Dfst.evaluate exDfst1 [D0,D1] @?= Just (E.fromList [B1,B0]))
      , testCase "C" (Dfst.evaluate exDfst3 [E2,E2,E2,E2,E2,E2] @?= Just (E.fromList [D1,D1,D1,D1,D1,D1]))
      , testCase "D" (Dfst.evaluate exDfst4 "Xfoo, " @?= Just (E.fromList (replicate 6 A0)))
      , testCase "E" (Dfst.evaluate exDfst4 "Xfoo,  " @?= Just (E.fromList (replicate 7 A0)))
      , testCase "F" (Dfst.evaluate SEN.liftedTransducer SEN.fastCat @?= Just (E.fromList SEN.fastCatExpected))
      , testCase "G" (Dfst.evaluate SEN.liftedTransducer SEN.slowDog @?= Just (E.fromList SEN.slowDogExpected))
      ]
    , testGroup "compact"
      [ testCase "A" (CDfst.evaluateList (CDfst.compact exDfst1) [D0,D2] @?= Nothing)
      , testCase "B" (CDfst.evaluateList (CDfst.compact exDfst1) [D0,D1] @?= Just (E.fromList [Ranged 0 1 B1,Ranged 1 1 B0]))
      , testCase "C" (CDfst.evaluateList (CDfst.compact exDfst3) [E2,E2,E2,E2,E2,E2] @?= Just (E.fromList [Ranged 0 6 D1]))
      , testCase "D" (CDfst.evaluateList (CDfst.compact exDfst4) "Xfoo, " @?= Just (E.fromList [Ranged 0 6 A0]))
      , testCase "E" (CDfst.evaluateList (CDfst.compact exDfst4) "Xfoo,  " @?= Just (E.fromList [Ranged 0 7 A0]))
      , testCase "F" (CDfst.evaluateList (CDfst.compact exDfst4) "Xfoo,   " @?= Just (E.fromList [Ranged 0 8 A0]))
      , TL.testProperty "G" $ \x -> let dfst = generateDfst1 x in fmap expandRanged (CDfst.evaluateList (CDfst.compact dfst) [A0,A0,A0]) == Dfst.evaluate dfst [A0,A0,A0]
      , testCase "H" (fmap expandRanged (CDfst.evaluateList SEN.compactTransducer SEN.fastCat) @?= Just (E.fromList SEN.fastCatExpected))
      , testCase "I" ((fmap.fmap) expandRanged (CUDfst.evaluateUtf8 SEN.compactUnboxedTransducer (Bytes.fromByteArray SEN.fastCatAscii)) @?= Right (Just (E.fromList SEN.fastCatExpected)))
      , testCase "J" ((fmap.fmap) expandRanged (CUDfst.evaluateAscii SEN.compactUnboxedTransducer (Bytes.fromByteArray SEN.fastCatAscii)) @?= Right (Just (E.fromList SEN.fastCatExpected)))
      ]
    , testGroup "union"
      [ testGroup "unit"
        [ testCase "A" (let x = Dfst.evaluate (Dfst.union (Dfst.map S.singleton exDfst1) (Dfst.map S.singleton exDfst2)) [D0,D1] in assertBool (show x) (setSubresult [B0, B1] x))
        , testCase "B" (let x = Dfst.evaluate (Dfst.union (Dfst.map S.singleton exDfst1) (Dfst.map S.singleton exDfst2)) [D0,D3] in assertBool (show x) (setSubresult [B0, B0] x))
        ]
      ]
    ]
  ]

expandRanged :: Array (Ranged a) -> Array a
expandRanged = foldMap $ \(Ranged _ len m) -> E.fromList (replicate len m)

subresult :: Ord a => [Set a] -> Maybe (Array (Set a)) -> Bool
subresult xs = \case
  Nothing -> False
  Just ys -> length xs == length ys && all (uncurry S.isSubsetOf) (zip xs (E.toList ys))

setSubresult :: Ord a => [a] -> Maybe (Array (Set a)) -> Bool
setSubresult xs = \case
  Nothing -> False
  Just ys -> length xs == length ys && all (uncurry S.member) (zip xs (E.toList ys))

lawsToTest :: QCC.Laws -> TestTree
lawsToTest (QCC.Laws name pairs) = testGroup name (map (uncurry TQC.testProperty) pairs)

instance (Arbitrary t, Bounded t, Enum t, Ord t) => Arbitrary (Dfsa t) where
  arbitrary = do
    let states = 6
    n <- QC.choose (0,30)
    (ts :: [(Int,Int,t,t)]) <- QC.vectorOf n $ (,,,)
      <$> QC.choose (0,states)
      <*> QC.choose (0,states)
      <*> QC.arbitrary
      <*> QC.arbitrary
    return $ Dfsa.build $ \s0 -> do
      states <- fmap (s0:) (replicateM states Dfsa.state)
      Dfsa.accept (states L.!! 3)
      forM_ ts $ \(source,dest,a,b) -> do
        let lo = min a b
            hi = max a b
        Dfsa.transition lo hi (states L.!! source) (states L.!! dest)

instance (Arbitrary t, Bounded t, Enum t, Ord t) => Arbitrary (Nfsa t) where
  arbitrary = do
    let states = 3
    n <- QC.choose (0,20)
    (ts :: [(Int,Int,t,t,Bool)]) <- QC.vectorOf n $ (,,,,)
      <$> QC.choose (0,states)
      <*> QC.choose (0,states)
      <*> QC.arbitrary
      <*> QC.arbitrary
      <*> QC.frequency [(975,pure False),(25,pure True)]
    return $ B.build $ \s0 -> do
      states <- fmap (s0:) (replicateM states B.state)
      B.accept (states L.!! 1)
      forM_ ts $ \(source,dest,a,b,epsilon) -> do
        let lo = min a b
            hi = max a b
        if epsilon
          then B.epsilon (states L.!! source) (states L.!! dest)
          else B.transition lo hi (states L.!! source) (states L.!! dest)

-- This instance is provided for testing. The library does not provide
-- an Eq instance for Nfsa since there is no efficent algorithm to do this
-- in general.
instance (Ord t, Bounded t, Enum t) => Eq (Nfsa t) where
  a == b = Nfsa.toDfsa a == Nfsa.toDfsa b

ex1 :: Nfsa D
ex1 = B.build $ \s0 -> do
  s1 <- B.state
  B.accept s1
  B.transition D1 D2 s0 s1
  B.transition D0 D0 s0 s0
  B.transition D3 D3 s1 s1

ex2 :: Nfsa D
ex2 = B.build $ \s0 -> do
  s1 <- B.state
  B.accept s1
  B.transition D1 D2 s0 s1
  B.transition D0 D0 s0 s0
  B.transition D3 D3 s0 s0
  B.transition D3 D3 s0 s1
  B.transition D3 D3 s1 s1

ex3 :: Nfsa D
ex3 = B.build $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s2
  B.transition D1 D2 s0 s1
  B.transition D3 D3 s1 s2
  B.transition D2 D3 s1 s0
  B.transition D0 D0 s2 s0
  B.epsilon s2 s1

ex4 :: Nfsa D
ex4 = B.build $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s1
  B.accept s2
  B.transition D1 D2 s0 s1
  B.transition D0 D0 s0 s0
  B.transition D3 D3 s1 s1
  B.transition D1 D2 s0 s2
  B.transition D3 D3 s2 s2

ex5 :: Nfsa D
ex5 = B.build $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s2
  B.transition D0 D1 s0 s1
  B.transition D1 D2 s1 s2

-- Note: ex5 and ex6 accept the same inputs.
ex6 :: Nfsa D
ex6 = B.build $ \s0 -> do
  -- s3, s4, and s5 are unreachable
  s3 <- B.state
  s4 <- B.state
  s5 <- B.state
  s2 <- B.state
  s1 <- B.state
  B.accept s2
  B.transition D0 D1 s0 s1
  B.transition D1 D2 s1 s2
  B.epsilon s3 s4
  B.transition D0 D2 s4 s5
  B.transition D2 D2 s5 s3
  B.transition D1 D2 s5 s3

ex7 :: Nfsa D
ex7 = B.build $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  s3 <- B.state
  s4 <- B.state
  s5 <- B.state
  B.accept s3
  B.accept s4
  B.transition D0 D0 s0 s1
  B.transition D0 D0 s0 s2
  B.transition D2 D2 s1 s3
  B.transition D0 D0 s1 s4
  B.transition D1 D1 s2 s4
  B.transition D3 D3 s1 s3
  B.transition D3 D3 s2 s5
  B.transition D2 D3 s4 s4
  B.epsilon s4 s5
  B.epsilon s5 s4


exDfsa1 :: Dfsa D
exDfsa1 = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  Dfsa.accept s1
  Dfsa.transition D0 D1 s0 s1

exDfsa2 :: Dfsa D
exDfsa2 = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  Dfsa.accept s2
  Dfsa.transition D0 D3 s0 s1
  Dfsa.transition D1 D2 s0 s2
  Dfsa.transition D2 D3 s1 s1
  Dfsa.transition D2 D2 s1 s2
  Dfsa.transition D3 D3 s2 s2

exDfsa3 :: Dfsa D
exDfsa3 = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  s3 <- Dfsa.state
  Dfsa.accept s1
  Dfsa.transition D1 D2 s0 s2
  Dfsa.transition D2 D3 s2 s1
  Dfsa.transition D3 D3 s3 s3
  Dfsa.transition D3 D3 s3 s3

exDfsa4 :: Dfsa D
exDfsa4 = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  s3 <- Dfsa.state
  Dfsa.accept s2
  Dfsa.accept s3
  Dfsa.transition D1 D1 s0 s1
  Dfsa.transition D2 D2 s0 s1
  Dfsa.transition D2 D2 s1 s2
  Dfsa.transition D3 D3 s1 s2

exDfsa5 :: Dfsa B
exDfsa5 = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  Dfsa.accept s2
  Dfsa.transition B0 B0 s0 s0
  Dfsa.transition B1 B1 s0 s1
  Dfsa.transition B0 B0 s1 s0
  Dfsa.transition B1 B1 s1 s2
  Dfsa.transition B0 B0 s2 s2
  Dfsa.transition B1 B1 s2 s0

exNfst1 :: Nfst D B
exNfst1 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  Nfst.accept s1
  Nfst.transition D0 D1 B0 s0 s1 
  Nfst.transition D2 D3 B1 s0 s1 
  Nfst.transition D0 D3 B1 s1 s1 

exNfst2 :: Nfst D B
exNfst2 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  Nfst.epsilon s0 s1
  Nfst.accept s2
  Nfst.transition D0 D1 B0 s0 s1 
  Nfst.transition D2 D3 B1 s0 s1 
  Nfst.transition D0 D0 B0 s1 s2 
  Nfst.transition D1 D3 B1 s1 s1
  Nfst.transition D0 D0 B0 s2 s2
  Nfst.transition D1 D3 B1 s2 s0

exNfst3 :: Nfst D B
exNfst3 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  s3 <- Nfst.state
  s4 <- Nfst.state
  Nfst.accept s3
  Nfst.accept s4
  Nfst.transition D0 D0 B0 s0 s1
  Nfst.transition D0 D0 B1 s0 s2
  Nfst.transition D2 D2 B1 s1 s3
  Nfst.transition D1 D1 B0 s2 s4
  Nfst.transition D3 D3 B0 s1 s3
  Nfst.transition D3 D3 B0 s2 s4

exNfst4 :: Nfst D (Set B)
exNfst4 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  s3 <- Nfst.state
  s4 <- Nfst.state
  s5 <- Nfst.state
  Nfst.accept s3
  Nfst.accept s4
  Nfst.transition D0 D0 (S.singleton B0) s0 s1
  Nfst.transition D0 D0 (S.singleton B1) s0 s2
  Nfst.transition D2 D2 (S.singleton B1) s1 s3
  Nfst.transition D0 D0 (S.singleton B0) s1 s4
  Nfst.transition D1 D1 (S.singleton B0) s2 s4
  Nfst.transition D3 D3 (S.singleton B0) s1 s3
  Nfst.transition D3 D3 (S.singleton B0) s2 s5
  Nfst.transition D2 D3 (S.singleton B1) s4 s4
  Nfst.epsilon s4 s5
  Nfst.epsilon s5 s4

exNfst5 :: Nfst D (Set B)
exNfst5 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  Nfst.accept s2
  Nfst.transition D1 D1 (S.singleton B0) s0 s1
  Nfst.transition D2 D2 (S.singleton B1) s1 s2

exNfst6 :: Nfst D (Set B)
exNfst6 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  s3 <- Nfst.state
  s4 <- Nfst.state
  s5 <- Nfst.state
  s6 <- Nfst.state
  Nfst.epsilon s0 s4
  Nfst.accept s2
  Nfst.accept s6
  Nfst.transition D1 D1 (S.singleton B1) s0 s1
  Nfst.transition D3 D3 (S.singleton B0) s0 s4
  Nfst.transition D2 D2 (S.singleton B1) s1 s2
  Nfst.transition D3 D3 (S.singleton B0) s1 s4
  Nfst.transition D2 D2 (S.singleton B1) s1 s2
  Nfst.transition D0 D1 (S.singleton B0) s4 s6
  Nfst.transition D1 D1 (S.singleton B1) s6 s4
  Nfst.transition D0 D0 (S.singleton B0) s4 s1

exDfst1 :: Dfst D B
exDfst1 = Dfst.build $ \s0 -> do
  s1 <- Dfst.state
  s2 <- Dfst.state
  s3 <- Dfst.state
  s4 <- Dfst.state
  Dfst.accept s3
  Dfst.accept s4
  Dfst.transition D0 D0 B0 s0 s1
  Dfst.transition D0 D0 B1 s0 s2
  Dfst.transition D2 D2 B1 s1 s3
  Dfst.transition D1 D1 B0 s2 s4
  Dfst.transition D3 D3 B0 s1 s3
  Dfst.transition D3 D3 B0 s2 s4

exDfst2 :: Dfst D B
exDfst2 = Dfst.build $ \s0 -> do
  s1 <- Dfst.state
  s2 <- Dfst.state
  Dfst.accept s2
  Dfst.transition D0 D0 B0 s0 s1
  Dfst.transition D1 D1 B1 s1 s2
  Dfst.transition D2 D2 B0 s2 s0

exDfst3 :: Dfst E D
exDfst3 = Dfst.build $ \s0 -> do
  s1 <- Dfst.state
  s2 <- Dfst.state
  s3 <- Dfst.state
  s4 <- Dfst.state
  s5 <- Dfst.state
  s6 <- Dfst.state
  Dfst.accept s6
  Dfst.transition E2 E2 D1 s0 s1
  Dfst.transition E2 E2 D1 s1 s2
  Dfst.transition E2 E2 D1 s2 s3
  Dfst.transition E2 E2 D1 s3 s4
  Dfst.transition E2 E2 D1 s4 s5
  Dfst.transition E2 E2 D1 s5 s6

exDfst4 :: Dfst Char A
exDfst4 = Dfst.buildDefaulted $ \s0 s5 -> do
  s1 <- Dfst.state
  s2 <- Dfst.state
  s3 <- Dfst.state
  s4 <- Dfst.state
  Dfst.accept s4
  Dfst.transition 'X' 'X' A0 s0 s1
  Dfst.transition ',' ',' A0 s1 s5
  Dfst.transition minBound (pred ',') A0 s1 s2
  Dfst.transition (succ ',') maxBound A0 s1 s2
  Dfst.transition ',' ',' A0 s2 s3
  Dfst.transition minBound (pred ',') A0 s2 s2
  Dfst.transition (succ ',') maxBound A0 s2 s2
  Dfst.transition (' ') (' ') A0 s3 s4
  Dfst.transition minBound (pred ' ') A0 s3 s5
  Dfst.transition (succ ' ') maxBound A0 s3 s5
  Dfst.transition (' ') (' ') A0 s4 s4
  Dfst.transition minBound (pred ' ') A0 s4 s5
  Dfst.transition (succ ' ') maxBound A0 s4 s5


-- This is not exhaustive, but it is pretty thorough.
generateDfst1 :: (B,B,B,B,B,B,B,B,B,B,B) -> Dfst A B
generateDfst1 (x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) = Dfst.build $ \s0 -> do
  s1 <- Dfst.state
  s2 <- Dfst.state
  s3 <- Dfst.state
  Dfst.accept s3
  Dfst.transition A0 A0 x0 s0 s0
  Dfst.transition A0 A0 x1 s0 s1
  Dfst.transition A0 A0 x2 s0 s3
  Dfst.transition A0 A0 x3 s1 s0
  Dfst.transition A0 A0 x4 s1 s2
  Dfst.transition A0 A0 x5 s1 s3
  Dfst.transition A0 A0 x6 s2 s0
  Dfst.transition A0 A0 x7 s2 s1
  Dfst.transition A0 A0 x8 s2 s3
  Dfst.transition A0 A0 x9 s3 s0
  Dfst.transition A0 A0 x10 s3 s1
  
-- This uses s3 as a dead state. So, we are roughly testing
-- all DFA with four nodes, a binary transition function,
-- and a single fixed end state.
mkBinDfsa :: ((D,D),(D,D),(D,D)) -> Dfsa B
mkBinDfsa (ws,xs,ys) = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  s3 <- Dfsa.state
  Dfsa.accept s1
  let resolve = \case
        D0 -> s0
        D1 -> s1
        D2 -> s2
        D3 -> s3
      binTransitions (a,b) s = do
        Dfsa.transition B0 B0 s (resolve a)
        Dfsa.transition B1 B1 s (resolve b)
  binTransitions ws s0
  binTransitions xs s1
  binTransitions ys s2
  Dfsa.transition B0 B1 s3 s3

-- This does not have a designated dead state. It is
-- used by tests that are exhaustive.
mkLittleBinDfsa :: ((C,C),(C,C),(C,C)) -> Dfsa B
mkLittleBinDfsa (ws,xs,ys) = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  Dfsa.accept s1
  let resolve = \case
        C0 -> s0
        C1 -> s1
        C2 -> s2
      binTransitions (a,b) s = do
        Dfsa.transition B0 B0 s (resolve a)
        Dfsa.transition B1 B1 s (resolve b)
  binTransitions ws s0
  binTransitions xs s1
  binTransitions ys s2
