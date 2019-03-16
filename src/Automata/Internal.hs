{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language ScopedTypeVariables #-}

module Automata.Internal
  ( -- * Types
    Dfsa(..)
  , Nfsa(..)
  , TransitionNfsa(..)
    -- * Builder Types
  , State(..)
  , Epsilon(..)
    -- * NFA Functions 
  , toDfsa
  , toDfsaMapping
  , append
  , empty
  , rejectionNfsa
  , unionNfsa
  , epsilonClosure
    -- * DFA Functions
  , union
  , intersection
  , acceptance
  , rejection
  , minimize
  , minimizeMapping
  , composeMapping
  , composeMappingLimited
  ) where

import Control.Applicative (liftA2)
import Control.Monad (forM_,(<=<))
import Control.Monad.ST (ST,runST)
import Control.Monad.Trans.Class (lift)
import Data.Foldable (foldl',toList)
import Data.Map (Map)
import Data.Primitive (MutablePrimArray,MutableArray)
import Data.Maybe (fromMaybe,isNothing,mapMaybe)
import Data.Primitive (Array,indexArray)
import Data.Semigroup (First(..))
import Data.Semiring (Semiring)
import Data.Set (Set)
import Data.STRef (STRef,newSTRef,readSTRef,writeSTRef)

import Debug.Trace

import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Strict as M
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Primitive.Contiguous as C
import qualified Data.Primitive as PM
import qualified Data.Map.Lifted.Lifted as MLL
import qualified GHC.Exts as E
import qualified Data.Semiring
import qualified Data.Primitive as PM

-- | Deterministic Finite State Automaton.
--
-- The start state is always zero.
data Dfsa t = Dfsa
  { dfaTransition :: !(Array (DM.Map t Int))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states.
  , dfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Show)

-- | Non-Deterministic Finite State Automaton.
--
-- Some notes on the implementation and design:
--
-- * You can transition to any non-negative number of states (including 0).
-- * There is only one start state.
-- * We use the Thompson encoding. This means that there is an epsilon
--   transition that consumes no input.
-- * We store the full epsilon closure for every state. This means that,
--   when evaluating the NFA, we do not ever need to compute the closure.
-- * There is no Eq instance for NFA. In general, this can take exponential
--   time. If you really need to do this, convert the NFA to a DFA.
--
-- Invariants:
-- 
-- * The start state is always the state at position 0.
-- * The length of nfaTransition is given by nfaStates.
data Nfsa t = Nfsa
  { nfaTransition :: !(Array (TransitionNfsa t))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states. The data structure inside is
    --   a diet map. This is capable of collapsing adjacent key-value
    --   pairs into ranges.
  , nfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Show)

data TransitionNfsa t = TransitionNfsa
  { transitionNfsaEpsilon :: {-# UNPACK #-} !(SU.Set Int)
  , transitionNfsaConsume :: {-# UNPACK #-} !(DM.Map t (SU.Set Int))
  } deriving (Eq,Show)

data Conversion = Conversion
  { _conversionLabel :: !Int
    -- The state identifier to be assigned to the next state.
  , conversionResolutions :: !(Map (SU.Set Int) Int)
    -- The map from subsets of states to new state identifiers.
    -- This is a bidirectional map.
  , conversionTraversed :: !(Set Int)
    -- The new state identifiers that have already been dealt with.
    -- This must be a subset of the keys of resolutions.
  , conversionPending :: !(Map Int (SU.Set Int))
    -- Newly created states that we need to consider transitions for.
    -- The keys in this should all be less than the label.
  }

data Pairing = Pairing
  { _pairingMap :: !(Map (Int,Int) Int)
  , _pairingReversedOld :: ![(Int,Int)]
  , _pairingState :: !Int
  }

append :: Nfsa t -> Nfsa t -> Nfsa t
append (Nfsa t1 f1) (Nfsa t2 f2) = 
  let n1 = C.size t1
      n2 = C.size t2
      n3 = n1 + n2
      f3 = SU.mapMonotonic (+n1) f2
      t3 = fmap (\(TransitionNfsa eps consume) -> TransitionNfsa (SU.mapMonotonic (+n1) eps) (DM.mapBijection (SU.mapMonotonic (+n1)) consume)) t2
      t4 = fmap (\(TransitionNfsa eps consume) -> TransitionNfsa eps (DM.mapBijection (\states -> if SU.null (SU.intersection states f1) then states else states <> transitionNfsaEpsilon (C.index t3 0)) consume)) t1
      !(# placeholder #) = C.index# t1 0
      t5 = runST $ do
        m <- C.replicateM n3 placeholder
        C.copy m 0 t4 0 n1
        C.copy m n1 t3 0 n2
        flip SU.traverse_ f1 $ \ix -> do
          TransitionNfsa epsilon consume <- C.read m ix
          let transition = TransitionNfsa (epsilon <> transitionNfsaEpsilon (C.index t3 0)) consume
          C.write m ix transition
        C.unsafeFreeze m
   in Nfsa t5 f3

nextIdentifier :: State.State Conversion Int
nextIdentifier = do
  Conversion n a b c <- State.get 
  State.put (Conversion (n + 1) a b c)
  return n

-- Mark a new state as having been completed.
complete :: Int -> State.State Conversion ()
complete s = do
  c <- State.get
  State.put c
    { conversionTraversed = S.insert s (conversionTraversed c)
    , conversionPending = M.delete s (conversionPending c)
    }

-- Convert the subset of NFA states to a single DFA state.
resolveSubset :: Array (TransitionNfsa t) -> SU.Set Int -> State.State Conversion Int
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
  
epsilonClosure :: Array (TransitionNfsa t) -> SU.Set Int -> SU.Set Int
epsilonClosure s states = go states SU.empty where
  go new old = if new == old
    then new
    else
      let together = old <> new
       in go (mconcat (map (\ident -> transitionNfsaEpsilon (indexArray s ident)) (SU.toList together)) <> together) together

data Node t = Node
  !Int -- identifier
  !(DM.Map t Int) -- transitions

-- | Convert an NFSA to a DFSA. For certain inputs, this causes
--   the number of states to blow up expontentially, so do not
--   call this on untrusted input.
toDfsa :: (Ord t, Bounded t, Enum t) => Nfsa t -> Dfsa t
toDfsa = snd . toDfsaMapping

toDfsaMapping :: forall t. (Ord t, Bounded t, Enum t) => Nfsa t -> (Map (SU.Set Int) Int, Dfsa t)
toDfsaMapping (Nfsa t0 f0) = runST $ do
  let ((len,nodes),c) = State.runState
        (go 0 [])
        (Conversion 1 (M.singleton startClosure 0) S.empty (M.singleton 0 startClosure))
      resolutions = conversionResolutions c
  marr <- C.new len
  forM_ nodes $ \(Node ident transitions) -> C.write marr ident transitions
  arr <- C.unsafeFreeze marr
  let f1 = SU.fromList (M.foldrWithKey (\k v xs -> if SU.null (SU.intersection k f0) then xs else v : xs) [] resolutions)
  let (canonB,r) = minimizeMapping arr f1
      canon = fmap (fromMaybe (error "toDfsaMapping: missing canon value") . flip M.lookup canonB) resolutions
  return (canon,r)
  where
  startClosure :: SU.Set Int
  startClosure = epsilonClosure t0 (SU.singleton 0)
  go :: Int -> [Node t] -> State.State Conversion (Int, [Node t])
  go !n !edges0 = do
    Conversion _ _ _ pending <- State.get
    case M.foldMapWithKey (\k v -> Just (First (k,v))) pending of
      Nothing -> return (n, edges0)
      Just (First (m,states)) -> do
        t <- DM.traverseBijection (resolveSubset t0) (mconcat (map (transitionNfsaConsume . indexArray t0) (SU.toList states)))
        complete m
        go (n + 1) (Node m t : edges0)

-- | This uses Hopcroft's Algorithm. It is like a smart constructor for Dfsa.
minimize :: (Ord t, Bounded t, Enum t) => Array (DM.Map t Int) -> SU.Set Int -> Dfsa t
minimize t0 f0 = snd (minimizeMapping t0 f0)

-- | This uses Hopcroft's Algorithm. It also provides the mapping from old
--   state number to new state number. We need this mapping for a special
--   NFST to DFST minimizer.
minimizeMapping :: forall t. (Ord t, Bounded t, Enum t) => Array (DM.Map t Int) -> SU.Set Int -> (Map Int Int, Dfsa t)
minimizeMapping t0 f0 =
  let !partitions0 = go (S.fromList [f1,S.difference q0 f1]) (S.singleton f1)
      -- We move the partition containing the start state to the front.
      !partitions1 = case L.find (S.member 0) partitions0 of
        Just startStates -> startStates : deletePredicate (\s -> S.member 0 s || S.null s) (S.toList partitions0)
        Nothing -> error "Automata.Nfsa.minimize: incorrect"
      -- Creates a map from old state to new state. This is not a bijection
      -- since two old states may map to the same new state. However, we
      -- may treat it as a bijection since at most one of the old states
      -- is preserved.
      assign :: Int -> Map Int Int -> [Set Int] -> Map Int Int
      assign !_ !m [] = m
      assign !ix !m (s : ss) = assign (ix + 1) (M.union (M.fromSet (const ix) s) m) ss
      assignments = assign 0 M.empty partitions1
      newTransitions0 = E.fromList (map (\s -> DM.map (\oldState -> fromMaybe (error "Automata.Nfsa.minimize: missing state") (M.lookup oldState assignments)) (PM.indexArray t1 (S.findMin s))) partitions1)
      canonization = establishOrder newTransitions0
      description = "[canonization=" ++ show canonization ++ "][assignments=" ++ show assignments ++ "]"
      newTransitions1 :: Array (DM.Map t Int) = C.map' (DM.mapBijection (\s -> fromMaybe (error ("Automata.Nfsa.minimize: canonization missing state [state=" ++ show s ++ "]" ++ description)) (M.lookup s canonization))) newTransitions0
      newTransitions2 = runST $ do
        marr <- C.replicateM (M.size canonization) (error ("Automata.Nfsa.minimize: uninitialized element " ++ description))
        flip C.itraverse_ newTransitions1 $ \ix dm -> C.write marr (fromMaybe (error ("Automata.Nfsa.minimize: missing state while rearranging [state=" ++ show ix ++ "]" ++ description)) (M.lookup ix canonization)) dm
        C.unsafeFreeze marr
      newAcceptingStates = foldMap (maybe SU.empty SU.singleton . (flip M.lookup canonization <=< flip M.lookup assignments)) f1
      finalCanonization = fmap (fromMaybe (error ("minimizeMapping: failed to connect the canons.\npartitions:\n" ++ show partitions1 ++ "\ninitial canon:\n" ++ show initialCanonization ++ "\nsecond canon:\n" ++ show canonization)) . (flip M.lookup canonization <=< flip M.lookup assignments)) initialCanonization
   in (finalCanonization,Dfsa newTransitions2 newAcceptingStates)
  where
  q0 = S.fromList (enumFromTo 0 (C.size t1 - 1))
  f1 = S.fromList (mapMaybe (\x -> M.lookup x initialCanonization) (SU.toList f0))
  -- Do we actually need to canonize the states twice? Yes, we do.
  t1' :: Array (DM.Map t Int)
  t1' = C.map' (DM.mapBijection (\s -> fromMaybe (error "Automata.Nfsa.minimize: t1 prime") (M.lookup s initialCanonization))) t0
  t1 = runST $ do
    marr <- C.replicateM (M.size initialCanonization) (error "Automata.Nfsa.minimize: t1 uninitialized element")
    flip C.itraverse_ t1' $ \ix dm -> case M.lookup ix initialCanonization of
      Nothing -> return ()
      Just newIx -> C.write marr newIx dm
    C.unsafeFreeze marr
  initialCanonization = establishOrder t0
  -- The inverted transitions has the destination state as well as
  -- all source states that lead to it when the token is consumed. 
  {-# SCC invertedTransitions #-}
  invertedTransitions :: DM.Map t (MLL.Map Int (Set Int))
  invertedTransitions = mconcat
    (toList (C.imap (\ix m -> DM.mapBijection (\dest -> MLL.singleton dest (S.singleton ix)) m) t1 :: Array (DM.Map t (MLL.Map Int (Set Int)))))
  -- The result of go is set of disjoint sets. It represents the equivalence classes
  -- that have been established. All references to any state in an equivalence class
  -- can be replaced with any of the other states in the same equivalence class.
  -- The implementation of go closely mirrors the Hopcroft's Algorithm psuedocode
  -- from Wikipedia: https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
  {-# SCC go #-}
  go :: forall s. Partitions s -> Set (Partition s) -> ST s (Set (Set Int))
  go !p1 !w1 = case S.minView w1 of
    Nothing -> p1
    Just (!a,!w2) ->
      let (!p2,!w3) = DM.foldl'
            (\(!p3,!w4) !m ->
              let !x = foldMap (\s -> fromMaybe S.empty (MLL.lookup s m)) a
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
intersection :: (Ord t, Bounded t, Enum t) => Dfsa t -> Dfsa t -> Dfsa t
intersection = compose (&&)

{-# NOINLINE errorThunkUnion #-}
errorThunkUnion :: a
errorThunkUnion = error "Automata.Dfsa.union: slot not filled"

-- | Accepts input that is accepted by either of the two argument DFAs. This is also known
--   as synchronous composition in the literature.
union :: (Ord t, Bounded t, Enum t) => Dfsa t -> Dfsa t -> Dfsa t
union = compose (||)

composeMapping :: (Ord t, Bounded t, Enum t) => (Bool -> Bool -> Bool) -> Dfsa t -> Dfsa t -> (Map (Int,Int) Int, Dfsa t)
composeMapping combineFinalMembership d1@(Dfsa t1 _) d2@(Dfsa t2 _) =
  let p = compositionReachable t1 t2
   in composeMappingCommon combineFinalMembership d1 d2 p

composeMappingLimited :: (Ord t, Bounded t, Enum t) => Int -> (Bool -> Bool -> Bool) -> Dfsa t -> Dfsa t -> Maybe (Map (Int,Int) Int, Dfsa t)
composeMappingLimited !maxStates combineFinalMembership d1@(Dfsa t1 _) d2@(Dfsa t2 _) = do
  p <- compositionReachableLimited maxStates t1 t2
  Just (composeMappingCommon combineFinalMembership d1 d2 p)

composeMappingCommon :: (Ord t, Bounded t, Enum t) => (Bool -> Bool -> Bool) -> Dfsa t -> Dfsa t -> Pairing -> (Map (Int,Int) Int, Dfsa t)
composeMappingCommon combineFinalMembership (Dfsa t1 f1) (Dfsa t2 f2) (Pairing oldToNew reversedOld n3) = runST $ do
  m <- PM.newArray n3 errorThunkUnion
  let go !_ [] = return ()
      go !ix ((stateA,stateB) : xs) = do
        PM.writeArray m ix (DM.unionWith (\x y -> fromMaybe (error "Automata.Dfsa.union: could not find pair in oldToNew") (M.lookup (x,y) oldToNew)) (PM.indexArray t1 stateA) (PM.indexArray t2 stateB))
        go (ix - 1) xs
  go (n3 - 1) reversedOld
  frozen <- PM.unsafeFreezeArray m
  let finals = SU.fromList (M.foldrWithKey (\(stateA,stateB) stateNew xs -> if combineFinalMembership (SU.member stateA f1) (SU.member stateB f2) then stateNew : xs else xs) [] oldToNew)
  let (secondMapping, r) = minimizeMapping frozen finals
  return (M.map (\x -> fromMaybe (error "composeMappingCommon: bad lookup") (M.lookup x secondMapping)) oldToNew, r)

compose :: (Ord t, Bounded t, Enum t) => (Bool -> Bool -> Bool) -> Dfsa t -> Dfsa t -> Dfsa t
compose combineFinalMembership a b = snd (composeMapping combineFinalMembership a b)

compositionReachable :: Ord t => Array (DM.Map t Int) -> Array (DM.Map t Int) -> Pairing
compositionReachable !a !b = State.execState (go 0 0) (Pairing M.empty [] 0) where
  go :: Int -> Int -> State.State Pairing ()
  go !stateA !stateB = do
    Pairing m xs s <- State.get
    case M.lookup (stateA,stateB) m of
      Just _ -> return ()
      Nothing -> do
        State.put (Pairing (M.insert (stateA,stateB) s m) ((stateA,stateB) : xs) (s + 1))
        DM.traverse_ (uncurry go) (DM.unionWith (,) (PM.indexArray a stateA) (PM.indexArray b stateB))

-- A variant of compositionReachable that aborts if the total number of
-- reachable states ever exceeds a specified threshold.
compositionReachableLimited :: Ord t => Int -> Array (DM.Map t Int) -> Array (DM.Map t Int) -> Maybe Pairing
compositionReachableLimited !maxStates !a !b =
  State.execStateT (go 0 0) (Pairing M.empty [] 0)
  where
  go :: Int -> Int -> State.StateT Pairing Maybe ()
  go !stateA !stateB = do
    Pairing m xs s <- State.get
    if s < maxStates
      then case M.lookup (stateA,stateB) m of
        Just _ -> return ()
        Nothing -> do
          State.put (Pairing (M.insert (stateA,stateB) s m) ((stateA,stateB) : xs) (s + 1))
          DM.traverse_ (uncurry go) (DM.unionWith (,) (PM.indexArray a stateA) (PM.indexArray b stateB))
      else lift Nothing

-- | Docs for this are at @Automata.Nfsa.union@.
unionNfsa :: (Bounded t) => Nfsa t -> Nfsa t -> Nfsa t
unionNfsa (Nfsa t1 f1) (Nfsa t2 f2) = Nfsa
  ( runST $ do
      -- This replicated transition metadata only ends up being
      -- the transition for the start state. At all other indices,
      -- the value is overridden.
      m <- C.replicateM (n1 + n2 + 1)
        ( TransitionNfsa
          (mconcat
            [ SU.mapMonotonic (+1) (transitionNfsaEpsilon (C.index t1 0))
            , SU.mapMonotonic (\x -> 1 + n1 + x) (transitionNfsaEpsilon (C.index t2 0))
            , SU.tripleton 0 1 (1 + n1)
            ]
          )
          (DM.pure SU.empty)
        )
      C.copy m 1 (fmap (translateTransitionNfsa 1) t1) 0 n1
      C.copy m (1 + n1) (fmap (translateTransitionNfsa (1 + n1)) t2) 0 n2
      C.unsafeFreeze m
  )
  (SU.mapMonotonic (+1) f1 <> SU.mapMonotonic (\x -> 1 + n1 + x) f2)
  where
  !n1 = PM.sizeofArray t1
  !n2 = PM.sizeofArray t2

translateTransitionNfsa :: Int -> TransitionNfsa t -> TransitionNfsa t
translateTransitionNfsa n (TransitionNfsa eps m) = TransitionNfsa
  (SU.mapMonotonic (+n) eps)
  (DM.mapBijection (SU.mapMonotonic (+n)) m)

-- | Automaton that accepts all input. This is the identity
-- for 'intersection'.
acceptance :: Bounded t => Dfsa t
acceptance = Dfsa (C.singleton (DM.pure 0)) (SU.singleton 0)

-- | Automaton that rejects all input. This is the identity
-- for 'union'.
rejection :: Bounded t => Dfsa t
rejection = Dfsa (C.singleton (DM.pure 0)) SU.empty

-- | Automaton that accepts the empty string and rejects all
-- other strings. This is the identity for 'append'.
empty :: Bounded t => Nfsa t
empty = Nfsa
  ( C.doubleton
    (TransitionNfsa (SU.singleton 0) (DM.pure (SU.singleton 1)))
    (TransitionNfsa (SU.singleton 1) (DM.pure SU.empty))
  )
  (SU.singleton 0)

-- | Docs for this are at @Automata.Nfsa.rejection@.
rejectionNfsa :: Bounded t => Nfsa t
rejectionNfsa = Nfsa
  (C.singleton (TransitionNfsa (SU.singleton 0) (DM.pure SU.empty)))
  SU.empty

-- | This uses 'union' for @plus@ and 'intersection' for @times@.
instance (Ord t, Enum t, Bounded t) => Semiring (Dfsa t) where
  plus = union
  times = intersection
  zero = rejection
  one = acceptance

-- | This uses @union@ for @plus@ and @append@ for @times@.
instance (Bounded t) => Semiring (Nfsa t) where
  plus = unionNfsa
  times = append
  zero = rejectionNfsa
  one = empty
  
data Epsilon = Epsilon !Int !Int

newtype State s = State Int

data Partition s = Partition
  !Int -- identifier, these are produced from a monotonically increasing source
  !(STRef s (Metadata s))

data Metadata s = Metadata
  !Int -- Current size of the partition
  !(MutablePrimArray s Int) -- Elements in the partition

-- A partitioning of contiguous machine integers
data Partitions s = Partitions
  !(MutablePrimArray s Int) -- singleton array with next partition identifier
  !(STRef s [Partition s])
  -- All of the partitions. On the wikipedia page for partition refinement,
  -- it claims that this needs to support cheap insertion into the middle
  -- of the array. However, I do not believe this is true. It should be
  -- fine to always cons onto the front of the list.
  !(MutableArray s (Partition s)) -- Map from element to set identifier
  !(MutablePrimArray s Int)
  -- Map from element to index in partition. This is only meaningful
  -- when you already know the partition that the element is in.

finishPartitions :: Partitions s -> ST s (Set (Set Int))
finishPartitions (Partitions _ ps _ _) = do
  

-- This starts out with just one big partition.
newPartitions :: Int -> ST s (Partitions s, Partition s)
newPartitions !total = do
  counter <- PM.newPrimArray 1
  PM.writePrimArray counter 0 (1 :: Int)
  let go !ix !arr = if ix >= 0
        then do
          PM.writePrimArray arr ix ix
          go (ix - 1) arr
        else pure ()
  allElements <- PM.newPrimArray total
  go (total - 1) allElements
  elementToIndex <- PM.newPrimArray total
  go (total - 1) elementToIndex
  meta0 <- newSTRef (Metadata total allElements)
  let p0 = Partition 0 meta0
  partitionList <- newSTRef [p0]
  elementToPartition <- PM.newArray total p0
  pure (Partitions counter partitionList elementToPartition elementToIndex, p0)
  
-- In the returned tuples, the first element is the already-existing partition
-- (which may have shrunk) and the second element is the newly-created partition.
splitPartitions :: forall s. Partitions s -> SU.Set Int -> ST s [(Partition s,Partition s)]
splitPartitions (Partitions counter partitionList elementToPartition elementToIndex) distinction = do
  c0 <- PM.readPrimArray counter 0
  partitionListA <- readSTRef partitionList
  (partitionListB, updatedPartitionPairs, c1) <- go c0 partitionListA [] M.empty (SU.toList distinction)
  PM.writePrimArray counter 0 c1
  writeSTRef partitionList partitionListB
  pure updatedPartitionPairs
  where
  -- Invariant: the keys of the recend partition map must match the
  -- partition identifiers in the values.
  go :: Int -> [Partition s] -> [(Partition s, Partition s)] -> Map Int (Partition s) -> [Int] -> ST s ([Partition s],[(Partition s, Partition s)],Int)
  go !cntr !plist !pnew !_ [] = pure (plist,pnew,cntr)
  go !cntr !plist !pnew !recent (x : xs) = do
    poriginal@(Partition pnum mreforiginal) <- PM.readArray elementToPartition x
    -- Remove the element from the original partition. To do
    -- this, we must look up its position, move the last element
    -- in the partition into this position and then update the
    -- position of what was previously the last element. 
    Metadata origSz origElems <- readSTRef mreforiginal
    origLast <- PM.readPrimArray origElems (origSz - 1)
    origIx <- PM.readPrimArray elementToIndex x
    PM.writePrimArray origElems origIx origLast
    PM.writePrimArray elementToIndex origLast origIx
    writeSTRef mreforiginal $! Metadata (origSz - 1) origElems
    case M.lookup pnum recent of
      Nothing -> do
        pelems <- PM.newPrimArray 1
        PM.writePrimArray pelems 0 x
        let m = Metadata 1 pelems
        mref <- newSTRef m
        let !p = Partition cntr mref
        -- Add the element to the new partition. It was removed
        -- earlier before the case statement.
        PM.writeArray elementToPartition x p
        PM.writePrimArray elementToIndex x 0
        go (cntr + 1) (p : plist) ((poriginal,p) : pnew) (M.insert pnum p recent) xs
      Just myPartition@(Partition _ metaref) -> do
        Metadata sz buf <- readSTRef metaref
        bufSz <- PM.getSizeofMutablePrimArray buf
        PM.writeArray elementToPartition x myPartition
        PM.writePrimArray elementToIndex x bufSz
        if bufSz < sz
          then do
            PM.writePrimArray buf bufSz x
            writeSTRef metaref $! Metadata (sz + 1) buf
          else do
            let newBufSz = bufSz * 2
            newBuf <- PM.newPrimArray newBufSz
            -- intentionally using the old buffer size as the index
            PM.writePrimArray newBuf bufSz x
            writeSTRef metaref $! Metadata (sz + 1) newBuf
        go cntr plist pnew recent xs

partitionCardinality :: Partition s -> ST s Int
partitionCardinality (Partition _ r) = do
  Metadata card _ <- readSTRef r
  pure card

