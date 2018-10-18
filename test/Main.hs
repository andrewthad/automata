{-# language DerivingStrategies #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}

import Automata.Nfsa (Nfsa)
import Automata.Nfst (Nfst)
import Automata.Dfsa (Dfsa)
import Automata.Dfst (Dfst)
import Test.Tasty (TestTree,defaultMain,testGroup,adjustOption)
import Test.Tasty.HUnit (testCase)
import Test.HUnit ((@?=),assertBool)
import Test.LeanCheck (Listable,(\/),cons0)
import Test.QuickCheck (Arbitrary)
import Data.Proxy (Proxy(..))
import Data.Set (Set)
import Data.Primitive (Array)
import Control.Monad (forM_,replicateM)
import Data.Monoid (All(..))

import qualified Automata.Nfsa as Nfsa
import qualified Automata.Nfst as Nfst
import qualified Automata.Dfsa as Dfsa
import qualified Automata.Dfst as Dfst
import qualified Automata.Nfsa.Builder as B
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
      [ testCase "A" (Nfsa.evaluate ex1 [T3,T1] @?= False)
      , testCase "B" (Nfsa.evaluate ex1 [T0,T1,T3] @?= True)
      , testCase "C" (Nfsa.evaluate ex1 [T1,T3,T3] @?= True)
      , testCase "D" (Nfsa.evaluate ex1 [T0,T0,T0] @?= False)
      , testCase "E" (Nfsa.evaluate ex1 [T0,T0] @?= False)
      , testCase "F" (Nfsa.evaluate ex1 [T1] @?= True)
      , testCase "G" (Nfsa.evaluate ex1 [T1,T3] @?= True)
      , testCase "H" (Nfsa.evaluate ex2 [T3,T3,T0] @?= False)
      , testCase "I" (Nfsa.evaluate ex2 [T3,T3,T2] @?= True)
      , testCase "J" (Nfsa.evaluate ex3 [T1] @?= False)
      , testCase "K" (Nfsa.evaluate ex3 [T1,T3] @?= True)
      , testCase "L" (Nfsa.evaluate ex3 [T1,T3,T0] @?= False)
      , testCase "M" (Nfsa.evaluate ex3 [T1,T3,T0,T2,T3] @?= True)
      , testCase "N" (Nfsa.evaluate ex3 [T1,T3,T3] @?= True)
      ]
    , testGroup "append"
      [ testCase "A" (Nfsa.evaluate (Nfsa.append ex1 ex2) [T0,T1,T3,T3,T3,T2] @?= True)
      , testCase "B" (Nfsa.evaluate (Nfsa.append ex1 ex2) [T0,T0,T3,T0] @?= False)
      , testCase "C" (Nfsa.evaluate (Nfsa.append ex1 ex2) [T1,T3] @?= True)
      , testCase "D" (Nfsa.evaluate (Nfsa.append ex2 ex3) [T3,T3,T2,T1,T3,T3] @?= True)
      , testCase "E" (Nfsa.evaluate (Nfsa.append ex2 ex3) [T3,T3,T2] @?= False)
      ]
    , testGroup "union"
      [ testGroup "unit"
        [ testCase "A" (Nfsa.evaluate (Nfsa.union ex1 ex2) [T3,T1] @?= True)
        , testCase "B" (Nfsa.evaluate (Nfsa.union ex1 ex2) [T3,T3,T2] @?= True)
        , testCase "C" (Nfsa.evaluate (Nfsa.union ex1 ex2) [T0,T0,T0] @?= False)
        ]
      ]
    , testGroup "toDfsa"
      [ testGroup "unit"
        [ testCase "A" (Dfsa.evaluate (Nfsa.toDfsa ex1) [T0,T1,T3] @?= True)
        , testCase "B" (Dfsa.evaluate (Nfsa.toDfsa ex1) [T3,T1] @?= False)
        , testCase "C" (Dfsa.evaluate (Nfsa.toDfsa (Nfsa.append ex1 ex2)) [T0,T1,T3,T3,T3,T2] @?= True)
        , testCase "D" (Dfsa.evaluate (Nfsa.toDfsa (Nfsa.append ex2 ex3)) [T3,T3,T2,T1,T3,T3] @?= True)
        , testCase "E" (Dfsa.evaluate (Nfsa.toDfsa (Nfsa.append ex1 ex2)) [T0,T0,T3,T0] @?= False)
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
      , lawsToTest (QCC.semiringLaws (Proxy :: Proxy (Nfsa T)))
      ]
    ]
  , testGroup "Dfsa"
    [ testGroup "evaluate"
      [ testCase "A" (Dfsa.evaluate exDfsa1 [T1] @?= True)
      , testCase "B" (Dfsa.evaluate exDfsa1 [T3,T2,T1,T2,T0] @?= True)
      , testCase "C" (Dfsa.evaluate exDfsa2 [T3,T3] @?= False)
      , testCase "D" (Dfsa.evaluate exDfsa2 [T1] @?= True)
      , testCase "E" (Dfsa.evaluate exDfsa2 [T0,T2] @?= True)
      ]
    , testGroup "union"
      [ testGroup "unit"
        [ testCase "A" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [T0,T1,T3] @?= True)
        , testCase "B" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [T2,T3] @?= True)
        , testCase "C" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [T1,T3] @?= True)
        , testCase "D" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [T1,T3,T0] @?= False)
        , testCase "E" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [T1] @?= True)
        , testCase "F" (Dfsa.evaluate (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3)) [T3] @?= False)
        , testCase "G" (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex3) @?= Dfsa.union (Nfsa.toDfsa ex3) (Nfsa.toDfsa ex1))
        , testCase "H" (Dfsa.union (Nfsa.toDfsa ex1) (Nfsa.toDfsa ex1) @?= (Nfsa.toDfsa ex1))
        , testCase "I" (Dfsa.union (Nfsa.toDfsa ex3) (Nfsa.toDfsa ex3) @?= (Nfsa.toDfsa ex3))
        ]
      , TL.testProperty "idempotent" $ \x -> let y = mkBinDfsa x in y == Dfsa.union y y
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
    , lawsToTest (QCC.semiringLaws (Proxy :: Proxy (Dfsa T)))
    ]
  , testGroup "Nfst"
    [ testGroup "evaluate"
      [ testCase "A" (Nfst.evaluate exNfst1 [T0,T1] @?= S.singleton [B1,B0])
      , testCase "B" (Nfst.evaluate exNfst1 [T2,T1,T3] @?= S.singleton [B1,B1,B1])
      , testCase "C" (Nfst.evaluate exNfst2 [T0,T0] @?= S.singleton [B0,B0])
      , testCase "D" (Nfst.evaluate exNfst2 [T1,T0] @?= S.fromList [[B0,B0],[B0,B1]])
      , testCase "E" (Nfst.evaluate exNfst3 [T0,T2] @?= S.singleton [B1,B0])
      , testCase "F" (Nfst.evaluate exNfst3 [T0,T1] @?= S.singleton [B0,B1])
      ]
    , testGroup "toDfst"
      [ testGroup "unit"
        [ testCase "A" (let x = Dfst.evaluate (Nfst.toDfst exNfst4) [T0,T1] in assertBool (show x) (setSubresult [B1, B0] x))
        , testCase "B" (let x = Dfst.evaluate (Nfst.toDfst exNfst5) [T1,T2] in assertBool (show x) (setSubresult [B0, B1] x))
        ]
      , testGroup "evaluation"
        [ TL.testProperty "4" $ \(input :: [T]) -> getAll (foldMap (\x -> All (subresult (L.reverse x) (Dfst.evaluate (Nfst.toDfst exNfst4) input))) (Nfst.evaluate exNfst4 input))
        , TL.testProperty "5" $ \(input :: [T]) -> getAll (foldMap (\x -> All (subresult (L.reverse x) (Dfst.evaluate (Nfst.toDfst exNfst5) input))) (Nfst.evaluate exNfst5 input))
        , TL.testProperty "6" $ \(input :: [T]) -> getAll (foldMap (\x -> All (subresult (L.reverse x) (Dfst.evaluate (Nfst.toDfst exNfst6) input))) (Nfst.evaluate exNfst6 input))
        ]
      ]
    ]
  , testGroup "Dfst"
    [ testGroup "evaluate"
      [ testCase "A" (Dfst.evaluate exDfst1 [T0,T2] @?= Nothing)
      , testCase "B" (Dfst.evaluate exDfst1 [T0,T1] @?= Just (E.fromList [B1,B0]))
      ]
    ]
  ]

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

data B = B0 | B1
  deriving stock (Eq,Ord,Enum,Bounded,Show)

data T = T0 | T1 | T2 | T3
  deriving stock (Eq,Ord,Enum,Bounded,Show)

instance Semigroup B where
  (<>) = max

instance Monoid B where
  mempty = minBound

instance Listable B where
  tiers = cons0 B0 \/ cons0 B1

instance Arbitrary B where
  arbitrary = QC.arbitraryBoundedEnum

instance Listable T where
  tiers = cons0 T0 \/ cons0 T1 \/ cons0 T2 \/ cons0 T3

instance Arbitrary T where
  arbitrary = QC.arbitraryBoundedEnum

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
    return $ B.run $ \s0 -> do
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

ex1 :: Nfsa T
ex1 = B.run $ \s0 -> do
  s1 <- B.state
  B.accept s1
  B.transition T1 T2 s0 s1
  B.transition T0 T0 s0 s0
  B.transition T3 T3 s1 s1

ex2 :: Nfsa T
ex2 = B.run $ \s0 -> do
  s1 <- B.state
  B.accept s1
  B.transition T1 T2 s0 s1
  B.transition T0 T0 s0 s0
  B.transition T3 T3 s0 s0
  B.transition T3 T3 s0 s1
  B.transition T3 T3 s1 s1

ex3 :: Nfsa T
ex3 = B.run $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s2
  B.transition T1 T2 s0 s1
  B.transition T3 T3 s1 s2
  B.transition T2 T3 s1 s0
  B.transition T0 T0 s2 s0
  B.epsilon s2 s1

ex4 :: Nfsa T
ex4 = B.run $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s1
  B.accept s2
  B.transition T1 T2 s0 s1
  B.transition T0 T0 s0 s0
  B.transition T3 T3 s1 s1
  B.transition T1 T2 s0 s2
  B.transition T3 T3 s2 s2

ex5 :: Nfsa T
ex5 = B.run $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s2
  B.transition T0 T1 s0 s1
  B.transition T1 T2 s1 s2

-- Note: ex5 and ex6 accept the same inputs.
ex6 :: Nfsa T
ex6 = B.run $ \s0 -> do
  -- s3, s4, and s5 are unreachable
  s3 <- B.state
  s4 <- B.state
  s5 <- B.state
  s2 <- B.state
  s1 <- B.state
  B.accept s2
  B.transition T0 T1 s0 s1
  B.transition T1 T2 s1 s2
  B.epsilon s3 s4
  B.transition T0 T2 s4 s5
  B.transition T2 T2 s5 s3
  B.transition T1 T2 s5 s3

ex7 :: Nfsa T
ex7 = B.run $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  s3 <- B.state
  s4 <- B.state
  s5 <- B.state
  B.accept s3
  B.accept s4
  B.transition T0 T0 s0 s1
  B.transition T0 T0 s0 s2
  B.transition T2 T2 s1 s3
  B.transition T0 T0 s1 s4
  B.transition T1 T1 s2 s4
  B.transition T3 T3 s1 s3
  B.transition T3 T3 s2 s5
  B.transition T2 T3 s4 s4
  B.epsilon s4 s5
  B.epsilon s5 s4


exDfsa1 :: Dfsa T
exDfsa1 = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  Dfsa.accept s1
  Dfsa.transition T0 T1 s0 s1

exDfsa2 :: Dfsa T
exDfsa2 = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  Dfsa.accept s2
  Dfsa.transition T0 T3 s0 s1
  Dfsa.transition T1 T2 s0 s2
  Dfsa.transition T2 T3 s1 s1
  Dfsa.transition T2 T2 s1 s2
  Dfsa.transition T3 T3 s2 s2

exNfst1 :: Nfst T B
exNfst1 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  Nfst.accept s1
  Nfst.transition T0 T1 B0 s0 s1 
  Nfst.transition T2 T3 B1 s0 s1 
  Nfst.transition T0 T3 B1 s1 s1 

exNfst2 :: Nfst T B
exNfst2 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  Nfst.epsilon s0 s1
  Nfst.accept s2
  Nfst.transition T0 T1 B0 s0 s1 
  Nfst.transition T2 T3 B1 s0 s1 
  Nfst.transition T0 T0 B0 s1 s2 
  Nfst.transition T1 T3 B1 s1 s1
  Nfst.transition T0 T0 B0 s2 s2
  Nfst.transition T1 T3 B1 s2 s0

exNfst3 :: Nfst T B
exNfst3 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  s3 <- Nfst.state
  s4 <- Nfst.state
  Nfst.accept s3
  Nfst.accept s4
  Nfst.transition T0 T0 B0 s0 s1
  Nfst.transition T0 T0 B1 s0 s2
  Nfst.transition T2 T2 B1 s1 s3
  Nfst.transition T1 T1 B0 s2 s4
  Nfst.transition T3 T3 B0 s1 s3
  Nfst.transition T3 T3 B0 s2 s4

exNfst4 :: Nfst T (Set B)
exNfst4 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  s3 <- Nfst.state
  s4 <- Nfst.state
  s5 <- Nfst.state
  Nfst.accept s3
  Nfst.accept s4
  Nfst.transition T0 T0 (S.singleton B0) s0 s1
  Nfst.transition T0 T0 (S.singleton B1) s0 s2
  Nfst.transition T2 T2 (S.singleton B1) s1 s3
  Nfst.transition T0 T0 (S.singleton B0) s1 s4
  Nfst.transition T1 T1 (S.singleton B0) s2 s4
  Nfst.transition T3 T3 (S.singleton B0) s1 s3
  Nfst.transition T3 T3 (S.singleton B0) s2 s5
  Nfst.transition T2 T3 (S.singleton B1) s4 s4
  Nfst.epsilon s4 s5
  Nfst.epsilon s5 s4

exNfst5 :: Nfst T (Set B)
exNfst5 = Nfst.build $ \s0 -> do
  s1 <- Nfst.state
  s2 <- Nfst.state
  Nfst.accept s2
  Nfst.transition T1 T1 (S.singleton B0) s0 s1
  Nfst.transition T2 T2 (S.singleton B1) s1 s2

exNfst6 :: Nfst T (Set B)
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
  Nfst.transition T1 T1 (S.singleton B1) s0 s1
  Nfst.transition T3 T3 (S.singleton B0) s0 s4
  Nfst.transition T2 T2 (S.singleton B1) s1 s2
  Nfst.transition T3 T3 (S.singleton B0) s1 s4
  Nfst.transition T2 T2 (S.singleton B1) s1 s2
  Nfst.transition T0 T1 (S.singleton B0) s4 s6
  Nfst.transition T1 T1 (S.singleton B1) s6 s4
  Nfst.transition T0 T0 (S.singleton B0) s4 s1

exDfst1 :: Dfst T B
exDfst1 = Dfst.build $ \s0 -> do
  s1 <- Dfst.state
  s2 <- Dfst.state
  s3 <- Dfst.state
  s4 <- Dfst.state
  Dfst.accept s3
  Dfst.accept s4
  Dfst.transition T0 T0 B0 s0 s1
  Dfst.transition T0 T0 B1 s0 s2
  Dfst.transition T2 T2 B1 s1 s3
  Dfst.transition T1 T1 B0 s2 s4
  Dfst.transition T3 T3 B0 s1 s3
  Dfst.transition T3 T3 B0 s2 s4

-- This uses s3 as a dead state. So, we are roughly testing
-- all DFA with three nodes, a binary transition function,
-- and a single fixed end state.
mkBinDfsa :: ((T,T),(T,T),(T,T)) -> Dfsa B
mkBinDfsa (ws,xs,ys) = Dfsa.build $ \s0 -> do
  s1 <- Dfsa.state
  s2 <- Dfsa.state
  s3 <- Dfsa.state
  Dfsa.accept s1
  let resolve = \case
        T0 -> s0
        T1 -> s1
        T2 -> s2
        T3 -> s3
      binTransitions (a,b) s = do
        Dfsa.transition B0 B0 s (resolve a)
        Dfsa.transition B1 B1 s (resolve b)
  binTransitions ws s0
  binTransitions xs s1
  binTransitions ys s2
  Dfsa.transition B0 B1 s3 s3



