module Automaton.Internal
  ( Nfa(..)
  , TransitionNfa(..)
  ) where

import Data.Diet.Map.Strict.Unboxed.Lifted as DM
import Data.Diet.Map.Strict.Unboxed.Unboxed as DMU

-- The start state is always zero.
data Dfa t = Dfa
  { dfaTransition :: !(Array (DMU.Map t Int))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states.
  , dfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Ord)

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
  } deriving (Eq,Ord)

data TransitionNfa = TransitionNfa
  { transitionNfaEpsilon :: {-# UNPACK #-} !(SU.Set Int)
  , transitionNfaConsume :: {-# UNPACK #-} !(DM.Map t (SU.Set Int))
  }

