module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Diagonal
public import CORALean.NN.Definitions.WeightAcc

@[expose] public section

/-!
# Fusing a linear layer into the accumulator

CORA's `W = layer.W * W; b = layer.W * b + layer.b`.
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

/-- Follow the accumulated map by `x ↦ W₂ x + b₂`. -/
def WeightAcc.pushLinear : WeightAcc α n d → Mat α m d → (Fin m → α) → WeightAcc α n m
  | .id, W₂, b₂ => .aff W₂ b₂
  | .aff W b, W₂, b₂ => .aff (W₂ * W) (W₂ *ᵥ b + b₂)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
