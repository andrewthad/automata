{-# language DerivingStrategies #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}

import Automata.Nfa (Nfa)
import Automata.Dfa (Dfa)
import Test.Tasty (TestTree,defaultMain,testGroup,adjustOption)
import Test.Tasty.HUnit (testCase)
import Test.HUnit ((@?=))
import Test.LeanCheck (Listable,(\/),cons0)
import Test.QuickCheck (Arbitrary)
import Data.Proxy (Proxy(..))
import Control.Monad (forM_,replicateM)

import qualified Automata.Nfa as Nfa
import qualified Automata.Dfa as Dfa
import qualified Automata.Nfa.Builder as B
import qualified Automata.Dfa.Builder as DB
import qualified Data.List as L
import qualified Test.Tasty.LeanCheck as TL
import qualified Test.QuickCheck as QC
import qualified Test.Tasty.QuickCheck as TQC
import qualified Test.QuickCheck.Classes as QCC

main :: IO ()
main = defaultMain
  $ adjustOption (\_ -> TL.LeanCheckTests 70000)
  $ tests 

tests :: TestTree
tests = testGroup "Automata"
  [ testGroup "Nfa"
    [ testGroup "evaluate"
      [ testCase "A" (Nfa.evaluate ex1 [T3,T1] @?= False)
      , testCase "B" (Nfa.evaluate ex1 [T0,T1,T3] @?= True)
      , testCase "C" (Nfa.evaluate ex1 [T1,T3,T3] @?= True)
      , testCase "D" (Nfa.evaluate ex1 [T0,T0,T0] @?= False)
      , testCase "E" (Nfa.evaluate ex1 [T0,T0] @?= False)
      , testCase "F" (Nfa.evaluate ex1 [T1] @?= True)
      , testCase "G" (Nfa.evaluate ex1 [T1,T3] @?= True)
      , testCase "H" (Nfa.evaluate ex2 [T3,T3,T0] @?= False)
      , testCase "I" (Nfa.evaluate ex2 [T3,T3,T2] @?= True)
      , testCase "J" (Nfa.evaluate ex3 [T1] @?= False)
      , testCase "K" (Nfa.evaluate ex3 [T1,T3] @?= True)
      , testCase "L" (Nfa.evaluate ex3 [T1,T3,T0] @?= False)
      , testCase "M" (Nfa.evaluate ex3 [T1,T3,T0,T2,T3] @?= True)
      , testCase "N" (Nfa.evaluate ex3 [T1,T3,T3] @?= True)
      ]
    , testGroup "append"
      [ testCase "A" (Nfa.evaluate (Nfa.append ex1 ex2) [T0,T1,T3,T3,T3,T2] @?= True)
      , testCase "B" (Nfa.evaluate (Nfa.append ex1 ex2) [T0,T0,T3,T0] @?= False)
      , testCase "C" (Nfa.evaluate (Nfa.append ex1 ex2) [T1,T3] @?= True)
      , testCase "D" (Nfa.evaluate (Nfa.append ex2 ex3) [T3,T3,T2,T1,T3,T3] @?= True)
      , testCase "E" (Nfa.evaluate (Nfa.append ex2 ex3) [T3,T3,T2] @?= False)
      ]
    , testGroup "toDfa"
      [ testCase "A" (Dfa.evaluate (Nfa.toDfa ex1) [T0,T1,T3] @?= True)
      , testCase "B" (Dfa.evaluate (Nfa.toDfa ex1) [T3,T1] @?= False)
      , testCase "C" (Dfa.evaluate (Nfa.toDfa (Nfa.append ex1 ex2)) [T0,T1,T3,T3,T3,T2] @?= True)
      , testCase "D" (Dfa.evaluate (Nfa.toDfa (Nfa.append ex2 ex3)) [T3,T3,T2,T1,T3,T3] @?= True)
      , testCase "E" (Dfa.evaluate (Nfa.toDfa (Nfa.append ex1 ex2)) [T0,T0,T3,T0] @?= False)
      , testCase "F" (Nfa.toDfa ex1 == Nfa.toDfa ex4 @?= True)
      , testCase "G" (Nfa.toDfa ex1 == Nfa.toDfa ex2 @?= False)
      , testCase "H" (Nfa.toDfa ex5 == Nfa.toDfa ex6 @?= True)
      ]
    ]
  , testGroup "Dfa"
    [ testGroup "evaluate"
      [ testCase "A" (Dfa.evaluate exDfa1 [T1] @?= True)
      , testCase "B" (Dfa.evaluate exDfa1 [T3,T2,T1,T2,T0] @?= True)
      , testCase "C" (Dfa.evaluate exDfa1 [T3,T3] @?= False)
      , testCase "D" (Dfa.evaluate exDfa2 [T1] @?= True)
      , testCase "E" (Dfa.evaluate exDfa2 [T0,T2] @?= True)
      ]
    , testGroup "union"
      [ testGroup "unit"
        [ testCase "A" (Dfa.evaluate (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex3)) [T0,T1,T3] @?= True)
        , testCase "B" (Dfa.evaluate (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex3)) [T2,T3] @?= True)
        , testCase "C" (Dfa.evaluate (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex3)) [T1,T3] @?= True)
        , testCase "D" (Dfa.evaluate (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex3)) [T1,T3,T0] @?= False)
        , testCase "E" (Dfa.evaluate (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex3)) [T1] @?= True)
        , testCase "F" (Dfa.evaluate (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex3)) [T3] @?= False)
        , testCase "G" (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex3) @?= Dfa.union (Nfa.toDfa ex3) (Nfa.toDfa ex1))
        , testCase "H" (Dfa.union (Nfa.toDfa ex1) (Nfa.toDfa ex1) @?= (Nfa.toDfa ex1))
        , testCase "I" (Dfa.union (Nfa.toDfa ex3) (Nfa.toDfa ex3) @?= (Nfa.toDfa ex3))
        ]
      , TL.testProperty "idempotent" $ \x -> let y = mkBinDfa x in y == Dfa.union y y
      , testGroup "identity"
        [ TL.testProperty "left" $ \x -> let y = mkBinDfa x in y == Dfa.union Dfa.rejection y
        , TL.testProperty "right" $ \x -> let y = mkBinDfa x in y == Dfa.union y Dfa.rejection
        ]
      ]
    , testGroup "intersection"
      [ TL.testProperty "idempotent" $ \x -> let y = mkBinDfa x in y == Dfa.intersection y y
      , testGroup "identity"
        [ TL.testProperty "left" $ \x -> let y = mkBinDfa x in y == Dfa.intersection Dfa.acceptance y
        , TL.testProperty "right" $ \x -> let y = mkBinDfa x in y == Dfa.intersection y Dfa.acceptance
        ]
      ]
    , lawsToTest (QCC.semiringLaws (Proxy :: Proxy (Dfa T)))
    ]
  ]

lawsToTest :: QCC.Laws -> TestTree
lawsToTest (QCC.Laws name pairs) = testGroup name (map (uncurry TQC.testProperty) pairs)

data B = B0 | B1
  deriving stock (Eq,Ord,Enum,Bounded,Show)

data T = T0 | T1 | T2 | T3
  deriving stock (Eq,Ord,Enum,Bounded,Show)

instance Listable B where
  tiers = cons0 B0 \/ cons0 B1

instance Arbitrary B where
  arbitrary = QC.arbitraryBoundedEnum

instance Listable T where
  tiers = cons0 T0 \/ cons0 T1 \/ cons0 T2 \/ cons0 T3

instance Arbitrary T where
  arbitrary = QC.arbitraryBoundedEnum

instance (Arbitrary t, Bounded t, Enum t, Ord t) => Arbitrary (Dfa t) where
  arbitrary = do
    n <- QC.choose (0,30)
    (ts :: [(Int,Int,t,t)]) <- QC.vectorOf n $ (,,,)
      <$> QC.choose (0,6)
      <*> QC.choose (0,6)
      <*> QC.arbitrary
      <*> QC.arbitrary
    return $ DB.run $ \s0 -> do
      states <- fmap (s0:) (replicateM 6 DB.state)
      DB.accept (states L.!! 3)
      forM_ ts $ \(source,dest,a,b) -> do
        let lo = min a b
            hi = max a b
        DB.transition lo hi (states L.!! source) (states L.!! dest)

ex1 :: Nfa T
ex1 = B.run $ \s0 -> do
  s1 <- B.state
  B.accept s1
  B.transition T1 T2 s0 s1
  B.transition T0 T0 s0 s0
  B.transition T3 T3 s1 s1

ex2 :: Nfa T
ex2 = B.run $ \s0 -> do
  s1 <- B.state
  B.accept s1
  B.transition T1 T2 s0 s1
  B.transition T0 T0 s0 s0
  B.transition T3 T3 s0 s0
  B.transition T3 T3 s0 s1
  B.transition T3 T3 s1 s1

ex3 :: Nfa T
ex3 = B.run $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s2
  B.transition T1 T2 s0 s1
  B.transition T3 T3 s1 s2
  B.transition T2 T3 s1 s0
  B.transition T0 T0 s2 s0
  B.epsilon s2 s1

ex4 :: Nfa T
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

ex5 :: Nfa T
ex5 = B.run $ \s0 -> do
  s1 <- B.state
  s2 <- B.state
  B.accept s2
  B.transition T0 T1 s0 s1
  B.transition T1 T2 s1 s2

-- Note: ex5 and ex6 accept the same inputs.
ex6 :: Nfa T
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

exDfa1 :: Dfa T
exDfa1 = DB.run $ \s0 -> do
  s1 <- DB.state
  DB.accept s1
  DB.transition T0 T1 s0 s1

exDfa2 :: Dfa T
exDfa2 = DB.run $ \s0 -> do
  s1 <- DB.state
  s2 <- DB.state
  DB.accept s2
  DB.transition T0 T3 s0 s1
  DB.transition T1 T2 s0 s2
  DB.transition T2 T3 s1 s1
  DB.transition T2 T2 s1 s2
  DB.transition T3 T3 s2 s2

-- This uses s3 as a dead state. So, we are roughly testing
-- all DFA with three nodes, a binary transition function,
-- and a single fixed end state.
mkBinDfa :: ((T,T),(T,T),(T,T)) -> Dfa B
mkBinDfa (ws,xs,ys) = DB.run $ \s0 -> do
  s1 <- DB.state
  s2 <- DB.state
  s3 <- DB.state
  DB.accept s1
  let resolve = \case
        T0 -> s0
        T1 -> s1
        T2 -> s2
        T3 -> s3
      binTransitions (a,b) s = do
        DB.transition B0 B0 s (resolve a)
        DB.transition B1 B1 s (resolve b)
  binTransitions ws s0
  binTransitions xs s1
  binTransitions ys s2
  DB.transition B0 B1 s3 s3

