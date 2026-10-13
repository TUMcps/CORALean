module

public import CORALean.NN.Definitions.WeightAcc

@[expose] public section

/-!
# The layer an accumulator is flushed as

CORA's `aux_getLinearLayer`: the identity layer when nothing was fused, the linear layer otherwise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer emitted for the accumulated map. -/
def WeightAcc.layer : WeightAcc α n d → WeightLayer α n d
  | .id => .identity
  | .aff W b => .linear W b

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
