module

public import Mathlib.Data.Matrix.Mul
public import CORALean.NN.Definitions.WeightLayer

@[expose] public section

/-!
# What a weight layer computes
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

/-- The layer's map: `W x + b`, `scale ⊙ x + offset`, `x`, or `f` entrywise. -/
def WeightLayer.eval : ∀ {n m : ℕ}, WeightLayer α n m → (Fin n → α) → (Fin m → α)
  | _, _, .linear W b, x => W *ᵥ x + b
  | _, _, .elementwiseAffine s o, x => fun i => s i * x i + o i
  | _, _, .identity, x => x
  | _, _, .activation f, x => fun i => f (x i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
