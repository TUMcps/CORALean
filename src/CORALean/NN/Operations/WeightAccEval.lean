import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import CORALean.NN.Definitions.WeightAcc

/-!
# The map an accumulator stands for
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

/-- `x ↦ x` for nothing fused, `x ↦ W x + b` otherwise. -/
def WeightAcc.eval : ∀ {n d : ℕ}, WeightAcc α n d → (Fin n → α) → (Fin d → α)
  | _, _, .id, x => x
  | _, _, .aff W b, x => W *ᵥ x + b

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
