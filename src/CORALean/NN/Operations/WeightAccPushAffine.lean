module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Diagonal
public import CORALean.NN.Definitions.WeightAcc

@[expose] public section

/-!
# Fusing an elementwise affine layer into the accumulator

CORA's `W = diag(scale) * W; b = scale .* b + offset`.
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

/-- Follow the accumulated map by `x ↦ scale ⊙ x + offset`. -/
def WeightAcc.pushAffine : WeightAcc α n d → (Fin d → α) → (Fin d → α) → WeightAcc α n d
  | .id, s, o => .aff (Matrix.diagonal s) o
  | .aff W b, s, o => .aff (Matrix.diagonal s * W) (fun i => s i * b i + o i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
