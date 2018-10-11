{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language ScopedTypeVariables #-}

module Automata.Internal
  ( -- * Types
    Dfa(..)
  , Nfa(..)
  , TransitionNfa(..)
    -- * NFA Functions 
  , toDfa
  , append
  , evaluate
    -- * DFA Functions
  , union
  , intersection
  , acceptance
  , rejection
  , minimize
  ) where

import Control.Applicative (liftA2)
import Control.Monad (forM_,(<=<))
import Control.Monad.ST (runST)
import Control.Monad.Trans.State.Strict (State)
import Data.Foldable (foldl',toList)
import Data.Map (Map)
import Data.Maybe (fromMaybe,isNothing,mapMaybe)
import Data.Primitive (Array,indexArray)
import Data.Semigroup (First(..))
import Data.Semiring (Semiring)
import Data.Set (Set)

import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Strict as M
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Unboxed.Lifted as MUL
import qualified Data.Primitive.Contiguous as C
import qualified Data.Primitive as PM
import qualified Data.Map.Lifted.Lifted as MLL
import qualified GHC.Exts as E
import qualified Data.Semiring

-- The start state is always zero.
data Dfa t = Dfa
  { dfaTransition :: !(Array (DM.Map t Int))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states.
  , dfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Show)

-- NFA representation decisions:
--
-- * You can transition to any non-negative number of states (including 0).
-- * There is only one start state.
-- * We use the Thompson encoding. This means that there is an epsilon
--   transition that consumes no input.
-- * There is no Eq instance for NFA. In general, this can take exponential
--   time. If you really need to do this, convert the NFA to a DFA.
--
-- Invariants:
-- 
-- * The start state is always the state at position 0.
-- * The length of nfaTransition is given by nfaStates.
data Nfa t = Nfa
  { nfaTransition :: !(Array (TransitionNfa t))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states. The data structure inside is
    --   a diet map. This is capable of collapsing adjacent key-value
    --   pairs into ranges.
  , nfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Show)

data TransitionNfa t = TransitionNfa
  { transitionNfaEpsilon :: {-# UNPACK #-} !(SU.Set Int)
  , transitionNfaConsume :: {-# UNPACK #-} !(DM.Map t (SU.Set Int))
  } deriving (Eq,Show)

data Conversion = Conversion
  { conversionLabel :: !Int
    -- The state identifier to be assigned to the next state.
  , conversionResolutions :: !(Map (SU.Set Int) Int)
    -- The map from subsets of states to new state identifiers.
  , conversionTraversed :: !(Set Int)
    -- The new state identifiers that have already been dealt with.
    -- This must be a subset of the keys of resolutions.
  , conversionPending :: !(Map Int (SU.Set Int))
    -- Newly created states that we need to consider transitions for.
    -- The keys in this should all be less than the label.
  }

append :: Nfa t -> Nfa t -> Nfa t
append (Nfa t1 f1) (Nfa t2 f2) = 
  let n1 = C.size t1
      n2 = C.size t2
      n3 = n1 + n2
      f3 = SU.mapMonotonic (+n1) f2
      t3 = fmap (\(TransitionNfa eps consume) -> TransitionNfa (SU.mapMonotonic (+n1) eps) (DM.mapBijection (SU.mapMonotonic (+n1)) consume)) t2
      !(# placeholder #) = C.index# t1 0
      t4 = runST $ do
        m <- C.replicateM n3 placeholder
        C.copy m 0 t1 0 n1
        C.copy m n1 t3 0 n2
        flip C.itraverse_ t1 $ \ix (TransitionNfa epsilon consume) -> do
          let transition = TransitionNfa (epsilon <> SU.singleton n1) consume
          C.write m ix transition
        C.unsafeFreeze m
   in Nfa t4 f3

nextIdentifier :: State Conversion Int
nextIdentifier = do
  Conversion n a b c <- State.get 
  State.put (Conversion (n + 1) a b c)
  return n

-- Mark a new state as having been completed.
complete :: Int -> State Conversion ()
complete s = do
  c <- State.get
  State.put c
    { conversionTraversed = S.insert s (conversionTraversed c)
    , conversionPending = M.delete s (conversionPending c)
    }

-- Convert the subset of NFA states to a single DFA state.
resolveSubset :: Array (TransitionNfa t) -> SU.Set Int -> State Conversion Int
resolveSubset transitions s0 = do
  let s = epsilonClosure transitions s0
  Conversion _ resolutions0 _ _ <- State.get
  case M.lookup s resolutions0 of
    Nothing -> do
      ident <- nextIdentifier
      c <- State.get
      State.put c
        { conversionResolutions = M.insert s ident (conversionResolutions c)
        , conversionPending = M.insert ident s (conversionPending c)
        }
      return ident
    Just ident -> return ident
  

epsilonClosure :: Array (TransitionNfa t) -> SU.Set Int -> SU.Set Int
epsilonClosure s states = go states SU.empty where
  go new old = if new == old
    then new
    else
      let together = old <> new
       in go (mconcat (map (\ident -> transitionNfaEpsilon (indexArray s ident)) (SU.toList together)) <> together) together

data Node t = Node
  !Int -- identifier
  !(DM.Map t Int) -- transitions

toDfa :: forall t. (Ord t, Bounded t, Enum t) => Nfa t -> Dfa t
toDfa (Nfa t0 f0) = runST $ do
  let ((len,nodes),c) = State.runState
        (go 0 [])
        (Conversion 1 (M.singleton startClosure 0) S.empty (M.singleton 0 startClosure))
  marr <- C.new len
  forM_ nodes $ \(Node ident transitions) -> C.write marr ident transitions
  arr <- C.unsafeFreeze marr
  let f1 = SU.fromList (M.foldrWithKey (\k v xs -> if SU.null (SU.intersection k f0) then xs else v : xs) [] (conversionResolutions c))
  return (minimize arr f1)
  where
  startClosure :: SU.Set Int
  startClosure = epsilonClosure t0 (SU.singleton 0)
  go :: Int -> [Node t] -> State Conversion (Int, [Node t])
  go !n !edges0 = do
    Conversion _ _ _ pending <- State.get
    case M.foldMapWithKey (\k v -> Just (First (k,v))) pending of
      Nothing -> return (n, edges0)
      Just (First (m,states)) -> do
        t <- DM.traverseBijection (resolveSubset t0) (mconcat (map (transitionNfaConsume . indexArray t0) (SU.toList states)))
        complete m
        go (n + 1) (Node m t : edges0)

evaluate :: (Foldable f, Ord t) => Nfa t -> f t -> Bool
evaluate (Nfa transitions finals) tokens = not $ SU.null $ SU.intersection
  ( foldl'
    ( \(active :: SU.Set Int) token -> mconcat $ SU.foldl'
      (\xs state -> DM.lookup token (transitionNfaConsume (C.index transitions state)) : xs)
      ([] :: [SU.Set Int])
      (epsilonClosure transitions active)
    ) (epsilonClosure transitions (SU.singleton 0)) tokens
  )
  finals

-- | This uses Hopcroft's Algorithm. It is like a smart constructor for Dfa.
minimize :: forall t. (Ord t, Bounded t, Enum t) => Array (DM.Map t Int) -> SU.Set Int -> Dfa t
minimize t0 f0 =
  let partitions0 = go (S.fromList [f1,S.difference q0 f1]) (S.singleton f1)
      -- We move the partition containing the start start to the front.
      partitions1 = case L.find (S.member 0) partitions0 of
        Just startStates -> startStates : deletePredicate (\s -> S.member 0 s || S.null s) (S.toList partitions0)
        Nothing -> error "Automata.Nfa.minimize: incorrect"
      -- Creates a map from old state to new state. This is not a bijection
      -- since two old states may map to the same new state. However, we
      -- may treat it as a bijection since at most one of the old states
      -- is preserved.
      assign :: Int -> Map Int Int -> [Set Int] -> Map Int Int
      assign !_ !m [] = m
      assign !ix !m (s : ss) = assign (ix + 1) (M.union (M.fromSet (const ix) s) m) ss
      assignments = assign 0 M.empty partitions1
      newTransitions0 = E.fromList (map (\s -> DM.map (\oldState -> fromMaybe (error "Automata.Nfa.minimize: missing state") (M.lookup oldState assignments)) (PM.indexArray t1 (S.findMin s))) partitions1)
      canonization = establishOrder newTransitions0
      description = "[canonization=" ++ show canonization ++ "][assignments=" ++ show assignments ++ "]"
      newTransitions1 :: Array (DM.Map t Int) = C.map' (DM.mapBijection (\s -> fromMaybe (error ("Automata.Nfa.minimize: canonization missing state [state=" ++ show s ++ "]" ++ description)) (M.lookup s canonization))) newTransitions0
      newTransitions2 = runST $ do
        marr <- C.replicateM (M.size canonization) (error ("Automata.Nfa.minimize: uninitialized element " ++ description))
        flip C.itraverse_ newTransitions1 $ \ix dm -> C.write marr (fromMaybe (error ("Automata.Nfa.minimize: missing state while rearranging [state=" ++ show ix ++ "]" ++ description)) (M.lookup ix canonization)) dm
        C.unsafeFreeze marr
      newAcceptingStates = foldMap (maybe SU.empty SU.singleton . (flip M.lookup canonization <=< flip M.lookup assignments)) f1
   in Dfa newTransitions2 newAcceptingStates
  where
  q0 = S.fromList (enumFromTo 0 (C.size t1 - 1))
  f1 = S.fromList (mapMaybe (\x -> M.lookup x initialCanonization) (SU.toList f0))
  t1' :: Array (DM.Map t Int)
  t1' = C.map' (DM.mapBijection (\s -> fromMaybe (error "Automata.Nfa.minimize: t1 prime") (M.lookup s initialCanonization))) t0
  t1 = runST $ do
    marr <- C.replicateM (M.size initialCanonization) (error "Automata.Nfa.minimize: t1 uninitialized element")
    flip C.itraverse_ t1' $ \ix dm -> case M.lookup ix initialCanonization of
      Nothing -> return ()
      Just newIx -> C.write marr newIx dm
    C.unsafeFreeze marr
  initialCanonization = establishOrder t0
  -- The inverted transitions has the destination state as well as
  -- all source states that lead to it when the token is consumed. 
  invertedTransitions :: DM.Map t (MLL.Map Int (Set Int))
  invertedTransitions = mconcat (toList (C.imap (\ix m -> DM.mapBijection (\dest -> MLL.singleton dest (S.singleton ix)) m) t1 :: Array (DM.Map t (MLL.Map Int (Set Int)))))
  -- The result of go is set of disjoint sets. It represents the equivalence classes
  -- that have been established. All references to any state in an equivalence class
  -- can be replaced with any of the other states in the same equivalence class.
  go :: Set (Set Int) -> Set (Set Int) -> Set (Set Int)
  go p1 w1 = case S.minView w1 of
    Nothing -> p1
    Just (a,w2) ->
      let (p2,w3) = DM.foldl'
            (\(p3,w4) m ->
              let x = foldMap (\s -> fromMaybe S.empty (MLL.lookup s m)) a
               in foldl'
                    (\(p4, w5) y ->
                      let diffYX = S.difference y x
                          intersectYX = S.intersection y x
                       in if not (S.disjoint x y) && not (S.null diffYX)
                            then
                              ( S.insert diffYX (S.insert intersectYX (S.delete y p4))
                              , if S.member y w5
                                  then S.insert diffYX (S.insert intersectYX (S.delete y w5))
                                  else if S.size intersectYX <= S.size diffYX
                                    then S.insert intersectYX w5
                                    else S.insert diffYX w5
                              )
                            else (S.insert y p4, w5)
                    ) (S.empty, w4) p3
            ) (p1,w2) invertedTransitions
       in go p2 w3

-- This gives a canonical order to the states. Any state missing from
-- the resulting map was not reachable. The map goes from old state
-- identifiers to new state identifiers. It is a bijection.
establishOrder :: Array (DM.Map t Int) -> Map Int Int
establishOrder t = go 0 [0] M.empty where
  go :: Int -> [Int] -> Map Int Int -> Map Int Int
  go !ident !unvisited0 !assignments = case unvisited0 of
    [] -> assignments
    state : unvisited1 -> if isNothing (M.lookup state assignments)
      then
        let unvisited2 = DM.foldl'
             (\unvisited s -> if isNothing (M.lookup s assignments) then s : unvisited else unvisited)
             unvisited1
             (PM.indexArray t state)
         in go (ident + 1) unvisited2 (M.insert state ident assignments)
      else go ident unvisited1 assignments

-- removeUnreachable :: Array (DM.Map t Int) -> SU.Set Int -> (Array (DM.Map t Int), SU.Set Int)

deletePredicate :: (a -> Bool) -> [a] -> [a]
deletePredicate _ [] = []
deletePredicate p (y:ys) = if p y then deletePredicate p ys else y : deletePredicate p ys

-- | Accepts input that is accepted by both of the two argument DFAs. This is also known
--   as completely synchronous composition in the literature.
intersection :: (Ord t, Bounded t, Enum t) => Dfa t -> Dfa t -> Dfa t
intersection (Dfa t1 f1) (Dfa t2 f2) = minimize
  (liftA2 (scoot n2) t1 t2)
  (SU.fromList (liftA2 (+) (map (* n2) (SU.toList f1)) (SU.toList f2)))
  where
  !n2 = PM.sizeofArray t2

-- Adjusts all the values in the first interval map by multiplying
-- them by the number of states in the second automaton. Then,
-- adds these to the states numbers from the second automaton
scoot :: Ord t => Int -> DM.Map t Int -> DM.Map t Int -> DM.Map t Int
scoot n2 d1 d2 = DM.unionWith (\s1 s2 -> n2 * s1 + s2) d1 d2

-- | Accepts input that is accepted by either of the two argument DFAs. This is also known
--   as synchronous composition in the literature.
union :: (Ord t, Bounded t, Enum t) => Dfa t -> Dfa t -> Dfa t
union (Dfa t1 f1) (Dfa t2 f2) = minimize
  (liftA2 (scoot n2) t1 t2)
  ( SU.fromList $
    (liftA2 (+) (map (* n2) (SU.toList f1)) (enumFromTo 0 (n2 - 1)))
    <>
    (liftA2 (+) (SU.toList f2) (map (* n2) (enumFromTo 0 (n1 - 1))))
  )
  where
  !n2 = PM.sizeofArray t2
  !n1 = PM.sizeofArray t1

-- | Automaton that accepts all input. This is the identity
-- element for 'intersection'.
acceptance :: Bounded t => Dfa t
acceptance = Dfa (C.singleton (DM.pure 0)) (SU.singleton 0)

-- | Automaton that rejects all input. This is the identity
-- element for 'union'.
rejection :: Bounded t => Dfa t
rejection = Dfa (C.singleton (DM.pure 0)) SU.empty

instance (Ord t, Enum t, Bounded t) => Semiring (Dfa t) where
  plus = union
  times = intersection
  zero = rejection
  one = acceptance

