module Nfa
  ( Nfa
  ) where

-- Can an NFA transition to zero states? Not sure.

data Nfa t = Nfa
  { _nfaStates :: !Int
    -- ^ The total number of states. This must be greater than
    --   or equal to 1.
  , _nfaTransition :: !(Array (DefaultedMap t))
    -- ^ Given a state and transition, this field tells you what
    --   state to go to next. The length of this array must match
    --   the total number of states.
  , _nfaFinal :: !(SU.Set Int)
    -- ^ A string that ends in any of these set of states is
    --   considered to have been accepted by the grammar.
  } deriving (Eq,Ord)
