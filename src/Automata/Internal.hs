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
  , complement
  , acceptance
  , rejection
  , minimize
  , minimizeMapping
  , composeMapping
  , composeMappingLimited
  ) where

import Automata.Internal.Partition (Partitions,partitionStates,partitionCardinality)
import Automata.Internal.Partition (splitPartitions)
import Automata.Internal.Partition (Partition,newPartitions,finishPartitions)
import Control.Monad (forM_,(<=<))
import Control.Monad.ST (ST,runST)
import Control.Monad.Trans.Class (lift)
import Data.Foldable (toList)
import Data.Map (Map)
import Data.Maybe (fromMaybe,isNothing,mapMaybe)
import Data.Primitive (Array,indexArray)
import Data.Semigroup (First(..))
import Data.Semiring (Semiring)
import Data.Set (Set)

import qualified Data.List as L
import qualified Data.Foldable as F
import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Strict as M
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Primitive.Contiguous as C
import qualified Data.Map.Lifted.Lifted as MLL
import qualified GHC.Exts as E
import qualified Data.Semiring
import qualified Data.Primitive as PM

-- | Deterministic Finite State Automaton.
data Dfsa t = Dfsa
  -- The start state is always zero.
  { dfaTransition :: !(Array (DM.Map t Int))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states.
  , dfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Show)

-- | Non-Deterministic Finite State Automaton.
data Nfsa t = Nfsa
  -- Some notes on the implementation and design:
  --
  -- You can transition to any non-negative number of states (including 0).
  -- There is only one start state.
  -- We use the Thompson encoding. This means that there is an epsilon
  -- transition that consumes no input.
  -- We store the full epsilon closure for every state. This means that,
  -- when evaluating the NFA, we do not ever need to compute the closure.
  -- There is no Eq instance for NFA. In general, this can take exponential
  -- time. If you really need to do this, convert the NFA to a DFA.
  --
  -- Invariants:
  --
  -- - The start state is always the state at position 0.
  -- - The length of nfaTransition is given by nfaStates.
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
        m <- C.replicateMutable n3 placeholder
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

complement :: Dfsa t -> Dfsa t
complement dfsa = Dfsa (dfaTransition dfsa) (SU.fromList [0..PM.sizeofArray (dfaTransition dfsa) - 1] SU.\\ dfaFinal dfsa)

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
minimizeMapping t0 f0
  | C.size t0 == 0 = error "Automata.Internal: tried to minimize DFSA with 0 states"
  | S.null f1 =
      -- When there are no final states, the solution is trivial. The DFSA
      -- is equivalent to one with a single unaccepting state.
      (M.fromSet (\_ -> 0) (S.fromList (enumFromTo 0 (C.size t0 - 1))),rejection)
  | M.size initialCanonization == S.size f1 =
      -- When all states are accepting, the solution is similarly trivial.
      -- The DFSA is equivalent to one with a single accepting state.
      (M.fromSet (\_ -> 0) (S.fromList (enumFromTo 0 (C.size t0 - 1))),acceptance)
  | otherwise =
      let !partitions0 = runST $ do
             (ps,_) <- newPartitions (C.size t1)
             -- This might behave incorrectly when either:
             -- 1. There are no final states.
             -- 2. All states are final states.
             -- We guard against these cases elsewhere since they are
             -- easy to check for.
             splitPartitions ps (SU.fromList (S.toList f1)) >>= \case
               [(_,p1)] -> go ps (S.singleton p1)
               rs -> error ("Automata.Internal: initial split behaved unexpectedly [splits=" ++ show (length rs) ++ ",finals=" ++ show (S.size f1) ++ "]")
          -- We move the partition containing the start state to the front.
          !partitions1 = case L.find (S.member 0) partitions0 of
            Just startStates ->
              startStates : deletePredicate (\s -> S.member 0 s || S.null s) partitions0
              -- startStates : deletePredicate (\s -> S.member 0 s || S.null s) (S.toList partitions0)
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
          description = "[original_state_cardinality=" ++ show (C.size t1) ++ "][new_transitions_cardinality=" ++ show (C.size newTransitions0) ++ "][inverted_transitions=" ++ show (DM.elems invertedTransitions) ++ "][initial_canonization=" ++ show initialCanonization ++ "][canonization=" ++ show canonization ++ "][assignments=" ++ show assignments ++ "][partitions=" ++ show partitions1 ++ "][new_transitions_0=" ++ show (fmap DM.elems newTransitions0) ++ "][t1=" ++ show (fmap DM.elems t1) ++ "]"
          newTransitions1 :: Array (DM.Map t Int) = C.map' (DM.mapBijection (\s -> fromMaybe (error ("Automata.Nfsa.minimize: canonization missing state [state=" ++ show s ++ "]" ++ description)) (M.lookup s canonization))) newTransitions0
          newTransitions2 = runST $ do
            marr <- C.replicateMutable (M.size canonization) (error ("Automata.Nfsa.minimize: uninitialized element " ++ description))
            flip C.itraverse_ newTransitions1 $ \ix dm -> C.write marr (fromMaybe (error ("Automata.Nfsa.minimize: missing state while rearranging [state=" ++ show ix ++ "]" ++ description)) (M.lookup ix canonization)) dm
            C.unsafeFreeze marr
          newAcceptingStates = foldMap (maybe SU.empty SU.singleton . (flip M.lookup canonization <=< flip M.lookup assignments)) f1
          finalCanonization = fmap (fromMaybe (error ("minimizeMapping: failed to connect the canons.\npartitions:\n" ++ show partitions1 ++ "\ninitial canon:\n" ++ show initialCanonization ++ "\nsecond canon:\n" ++ show canonization)) . (flip M.lookup canonization <=< flip M.lookup assignments)) initialCanonization
       in (finalCanonization,Dfsa newTransitions2 newAcceptingStates)
  where
  -- q0 = S.fromList (enumFromTo 0 (C.size t1 - 1))
  f1 = S.fromList (mapMaybe (\x -> M.lookup x initialCanonization) (SU.toList f0))
  -- Do we actually need to canonize the states twice? Yes, we do.
  t1' :: Array (DM.Map t Int)
  t1' = C.map' (DM.mapBijection (\s -> fromMaybe (error "Automata.Nfsa.minimize: t1 prime") (M.lookup s initialCanonization))) t0
  t1 = runST $ do
    marr <- C.replicateMutable (M.size initialCanonization) (error "Automata.Nfsa.minimize: t1 uninitialized element")
    flip C.itraverse_ t1' $ \ix dm -> case M.lookup ix initialCanonization of
      Nothing -> return ()
      Just newIx -> C.write marr newIx dm
    C.unsafeFreeze marr
  initialCanonization = establishOrder t0
  -- The inverted transitions has the destination state as well as
  -- all source states that lead to it when the token is consumed.
  -- This can lead to some pretty nasty constant factor overheads
  -- when a large number of individual letters in an alphabet are
  -- used. There may be a way to improve this.
  {-# SCC invertedTransitions #-}
  invertedTransitions :: DM.Map t (MLL.Map Int (Set Int))
  invertedTransitions = mconcat
    (toList (C.imap (\ix m -> DM.mapBijection (\dest -> MLL.singleton dest (S.singleton ix)) m) t1 :: Array (DM.Map t (MLL.Map Int (Set Int)))))
  -- The result of go is set of disjoint sets. It represents the equivalence classes
  -- that have been established. All references to any state in an equivalence class
  -- can be replaced with any of the other states in the same equivalence class.
  -- The implementation of go closely mirrors the Hopcroft's Algorithm psuedocode
  -- from Wikipedia: https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
  go :: forall s. Partitions s -> Set (Partition s) -> ST s [Set Int]
  go !p !w1 = case S.minView w1 of
    Nothing -> do
      traceST "finished with go"
      finishPartitions p
    Just (!a,!w2) -> do
      traceST ("w2: " ++ show w2)
      statesA <- partitionStates a
      traceST ("considering partition " ++ show a ++ " with states " ++ show statesA)
      !w3 <- DM.foldlM'
        (\ !w4 !m -> do
          let !x = C.foldMap (\s -> fromMaybe S.empty (MLL.lookup s m)) statesA
          updates <- splitPartitions p (SU.fromList (S.toList x))
          F.foldlM
            (\ !w5 (!old,!new) -> do
              traceST ("w5: " ++ show w5)
              newCard <- partitionCardinality new
              oldCard <- partitionCardinality old
              pure $ if newCard == 0
                then error "Automata.Internal: new cardinality should not be zero"
                else if S.member old w5
                  then if oldCard == 0
                    then S.insert new (S.delete old w5)
                    else S.insert new w5
                  else if oldCard == 0
                    then w5
                    else if oldCard < newCard
                      then S.insert old w5
                      else S.insert new w5
            ) w4 updates
        ) w2 invertedTransitions
      go p w3

-- The traceST hackery is used for debugging.
traceST :: String -> ST s ()
traceST _ = pure ()
-- traceST str = unsafeIOToST (putStrLn str)

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
      m <- C.replicateMutable (n1 + n2 + 1)
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
