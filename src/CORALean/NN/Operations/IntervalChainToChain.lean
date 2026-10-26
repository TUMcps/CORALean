module

public import CORALean.NN.Definitions.IntervalChain
public import CORALean.NN.Definitions.Chain

@[expose] public section

/-!
# The functions an interval chain's layers compute

The `Chain` of an `IntervalChain`: a linear layer is `y ↦ W y + b`, an activation applies `σ`
entrywise. It is how a chain built for the interval backpropagation is read as the chain of
functions that `Chain.backprop` and `Chain.sensitivity` take.

## Inputs
* none

## Output
* chain of the layers' functions
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Real.IntervalChain.toChain : ∀ {n k : ℕ}, Real.IntervalChain n k → Chain n k
  | _, _, .nil => .nil
  | _, _, .linear W b rest => .cons (fun y => W *ᵥ y + b) rest.toChain
  | _, _, .act σ _ rest => .cons (fun y i => σ (y i)) rest.toChain

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
