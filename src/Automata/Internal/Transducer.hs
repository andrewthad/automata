module Automata.Internal.Transducer
  ( Nfst(..)
  , TransitionNfst(..)
  , epsilonClosure
  ) where

import Data.Primitive (Array)
import Data.Primitive (indexArray)
import qualified Data.Set.Unboxed as SU
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Lifted.Unlifted as MLN

-- | A finite state transducer. The @t@ represents the input token on
-- which a transition occurs. The @m@ represents the output token that
-- is generated when a transition is taken. On an epsilon transation,
-- no output is generated.
data Nfst t m = Nfst
  { nfstTransition :: !(Array (TransitionNfst t m))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states. The data structure inside is
    --   a diet map. This is capable of collapsing adjacent key-value
    --   pairs into ranges.
  , nfstFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Show)

data TransitionNfst t m = TransitionNfst
  { transitionNfstEpsilon :: {-# UNPACK #-} !(SU.Set Int)
  , transitionNfstConsume :: {-# UNPACK #-} !(DM.Map t (MLN.Map m (SU.Set Int)))
  } deriving (Eq,Show)

epsilonClosure :: Array (TransitionNfst m t) -> SU.Set Int -> SU.Set Int
epsilonClosure s states = go states SU.empty where
  go new old = if new == old
    then new
    else
      let together = old <> new
       in go (mconcat (map (\ident -> transitionNfstEpsilon (indexArray s ident)) (SU.toList together)) <> together) together
