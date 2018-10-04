module Nfa
  ( Nfa
  , append
  , toDfa
  ) where

import Automaton.Internal (Nfa(..),TransitionNfa(..))

fromDfa :: Dfa t -> Nfa t
fromDfa (Dfa t f) = Nfa (fmap (TransitionNfa SU.empty) t) f

data DirectedEdge t = DirectedEdge
  t -- inclusive low
  t -- inclusive high
  !Int -- from
  !Int -- to

data Conversion = Conversion
  { conversionLabel :: !Int
  , conversionResolutions :: !(Map (Set Int) Int)
  , conversionUnresolved :: !(Set (Set Int))
  }

nextIdentifier :: State Conversion Int
nextIdentifier = do
  Conversion n a b <- State.get 
  State.put (Conversion (n + 1) a b)
  return n

resolveSubset :: Set (Set Int) -> State Conversion Int
resolveSubset s = do
  Conversion _ resolutions0 _ <- State.get
  m <- M.alterF
    (\case
      Nothing -> fmap Just nextIdentifier
      Just m -> return (Just m)
    ) s resolutions0
  c <- State.get
  State.put c
    { conversionResolutions = M.insert s m (conversionResolutions c)
    , conversionUnresolved = S.delete s (conversionUnresolved c)
    }
  return m

subsetTransitions :: Set Int -> Array (TransitionNfa t) -> [(t,t)]
subsetTransitions ixs ts = foldMap
  ( \ix -> indexArray 
  ) ixs

-- This is a hack used to work around the collapsing behavior of diet maps.
data Unequal = Unequal

instance Eq Unequal where
  _ == _ = False

instance Semigroup Unequal where
  _ <> _ = Unequal

toDfa :: Nfa t -> Dfa t
toDfa (Nfa t0 f0) = go [] where
  move :: Int -> t -> t -> State (Conversion t) Int
  move !state !lo !hi = case 
  
  go :: [DirectedEdge t] -> State Conversion ()
  go !edges0 = do
    Conversion _ _ unresolved0 <- State.get
    if S.null unresolved0
      then return ()
      else do
        edges1 <- foldlM
          ( \edges states -> do
            m <- resolveSubset states
            n <- move m _ _
          ) edges0 unresolved0
        go edges1

append :: Nfa t -> Nfa t -> Nfa t
append (Nfa t1 f1) (Nfa t2 f2) = 
  let f3 = SU.mapMonotonic (+n) f2
      n1 = sizeofArray t1
      n2 = sizeofArray t2
      n3 = n1 + n2
      !(# placeholder #) = indexArray## t1 0
      t3 = runST $ do
        m <- newArray n3 placeholder
        copyArray m 0 t1 0 n1
        copyArray m n1 t2 0 n2
        forM_ t1 $ \ix -> do
          TransitionNfa epsilon consume <- indexArrayM t1 ix
          let transition = TransitionNfa (S.singleton epsilon <> S.singleton n1) consume
          writeArray m ix transition
        unsafeFreeze m
   in Nfa t3 f3

