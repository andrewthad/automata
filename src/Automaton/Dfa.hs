module Dfa
  ( Dfa
  , zero
  , one
  ) where

import qualified Vector.Length as Length
import qualified Vector.Index as Index
import qualified Data.Set.Unboxed as SU


instance Semigroup (Dfa t) where
  (<>) = union

instance Monoid (Dfa t) where
  mempty = bottom
  
data DefaultedMap t = DefaultedMap
  { _defaultedMapDefault :: {-# UNPACK #-} !Int
  , _defaultedMapMap :: {-# UNPACK #-} !(MUL.Map t Int)
  }

automaton :: Int -> Int -> Dfa t
automaton 

-- | Rejects all input.
zero :: Dfa t
zero = Dfa 1 (pure (DefaultedMap 0 MUL.empty)) SU.empty

-- | Accepts all input. I don't think this is actually the multiplicative identity.
one :: Dfa t
one = Dfa 1 (pure (DefaultedMap 0 MUL.empty)) (SU.singleton 0)

-- | Sequence the two automata. This runs the first one and then
--   runs the second one on the remaining input if the first one
--   was in an accepting state after consuming input. The maintainer
--   of this library is not sure what this is called in the literature.
append :: Dfa t -> Dfa t -> Dfa t
append (Dfa n1 t1 f1) (Dfa n2 t2 f2) =
  let f3 = SU.mapMonotonic (+1) f2
      n3 = n1 + n2
      !(# placeholder #) = indexArray## t1 0
      t3 = runST $ do
        m <- newArray n3 placeholder
        copyArray m 0 t1 0 n1
        copyArray m n1 t2 0 n2
        unsafeFreeze m
   in normalize (Dfa n3 t3 f3)

-- | Accepts input that is accepted by both of the argument DFAs. This is known
--   as completely synchronous composition in the literature.
product :: Dfa t -> Dfa t -> Dfa t
product (Dfa n1 t1 f1) (Dfa n2 t2 f2) = _

-- | Accepts input that is accepted by either of the two argument DFAs. This is known
--   as synchronous composition in the literature.
sum :: Dfa t -> Dfa t -> Dfa t
sum (Dfa n1 t1 f1) (Dfa n2 t2 f2) = Dfa
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

