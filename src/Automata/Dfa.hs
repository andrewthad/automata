{-# language BangPatterns #-}
{-# language MagicHash #-}
{-# language ScopedTypeVariables #-}
{-# language UnboxedTuples #-}

module Automata.Dfa
  ( Dfa
  , evaluate
  , union
  , intersection
  , acceptance
  , rejection
  ) where

import Automata.Internal (Dfa(..),union,intersection,acceptance,rejection)
import Data.Foldable (foldl')

import qualified Data.Primitive.Contiguous as C
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Set.Unboxed as SU

evaluate :: (Foldable f, Ord t) => Dfa t -> f t -> Bool
evaluate (Dfa transitions finals) tokens = SU.member
  (foldl' (\(active :: Int) token -> DM.lookup token (C.index transitions active)) 0 tokens)
  finals

-- instance Semigroup (Dfa t) where
--   (<>) = union
-- 
-- instance Monoid (Dfa t) where
--   mempty = bottom
--   
-- data DefaultedMap t = DefaultedMap
--   { _defaultedMapDefault :: {-# UNPACK #-} !Int
--   , _defaultedMapMap :: {-# UNPACK #-} !(MUL.Map t Int)
--   }
-- 
-- -- automaton :: Int -> Int -> Dfa t
-- -- automaton 
-- 
-- -- | Rejects all input.
-- zero :: Dfa t
-- zero = Dfa 1 (pure (DefaultedMap 0 MUL.empty)) SU.empty
-- 
-- -- | Accepts all input. I don't think this is actually the multiplicative identity.
-- one :: Dfa t
-- one = Dfa 1 (pure (DefaultedMap 0 MUL.empty)) (SU.singleton 0)
-- 
-- -- | Sequence the two automata. This runs the first one and then
-- --   runs the second one on the remaining input if the first one
-- --   was in an accepting state after consuming input. The maintainer
-- --   of this library is not sure what this is called in the literature.
-- append :: Dfa t -> Dfa t -> Dfa t
-- append (Dfa n1 t1 f1) (Dfa n2 t2 f2) =
--   let f3 = SU.mapMonotonic (+1) f2
--       n3 = n1 + n2
--       !(# placeholder #) = indexArray## t1 0
--       t3 = runST $ do
--         m <- newArray n3 placeholder
--         copyArray m 0 t1 0 n1
--         copyArray m n1 t2 0 n2
--         unsafeFreeze m
--    in normalize (Dfa n3 t3 f3)
-- 
-- -- | Accepts input that is accepted by both of the argument DFAs. This is known
-- --   as completely synchronous composition in the literature.
-- product :: Dfa t -> Dfa t -> Dfa t
-- product (Dfa n1 t1 f1) (Dfa n2 t2 f2) = _
-- 
-- -- normalize :: Dfa t -> Dfa t
-- -- normalize (Dfa n1 t1 f1)

