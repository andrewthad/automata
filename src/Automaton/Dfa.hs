module Dfa
  ( Dfa
  , bottom
  , top
  ) where

import qualified Vector.Length as Length
import qualified Vector.Index as Index
import qualified Data.Set.Unboxed as SU

-- The start state is always zero.
data Dfa t = Dfa
  { _dfaStates :: !Int
    -- ^ The total number of states. This must be greater than
    --   or equal to 1.
  , _dfaTransition :: !(Array (DefaultedMap t))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states.
  , _dfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Ord)

instance Semigroup (Dfa t) where
  (<>) = union

instance Monoid (Dfa t) where
  mempty = bottom
  
data DefaultedMap t = DefaultedMap
  { _defaultedMapDefault :: !Int
  , _defaultedMapMap :: {-# UNPACK #-} !(MUL.Map t Int)
  }

automaton :: Int -> Int -> Dfa t
automaton

bottom :: Dfa t
bottom = Dfa 1 (pure (DefaultedMap 0 MUL.empty)) SU.empty

top :: Dfa t
top = Dfa 1 (pure (DefaultedMap 0 MUL.empty)) (SU.singleton 0)

union :: Dfa t -> Dfa t -> Dfa t
union (Dfa n1 t1 f1) (Dfa n2 t2 f2) = Dfa
  (n1 * n2)
  (liftA2 (unionDefaulted n2) t1 t2)
  (SU.fromList (liftA2 (+) (map (* n2) (SU.toList f1)) (SU.toList f2)))

unionDefaulted :: Int -> DefaultedMap t -> DefaultedMap t -> DefaultedMap t
unionDefaulted n2 (DefaultedMap d1 m1) (DefaultedMap d2 m2) =
  DefaultedMap
    (n2 * d1 + d2)
    ( mconcat
      [ (MUU.unionWith (\s1 s2 -> n2 * s1 + s2) m1 m2)
      ]
    )

-- normalize :: Dfa t -> Dfa t
-- normalize (Dfa n1 t1 f1)

