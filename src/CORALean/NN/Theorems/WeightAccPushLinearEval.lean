import CORALean.NN.Operations.WeightAccPushLinear
import CORALean.NN.Operations.WeightAccEval

/-!
# Fusing a linear layer composes the maps

`W₂ (W x + b) + b₂ = (W₂ W) x + (W₂ b + b₂)`, exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The pushed accumulator is the accumulated map followed by `x ↦ W₂ x + b₂`. -/
theorem WeightAcc.pushLinear_eval (acc : WeightAcc α n d) (W₂ : Mat α m d) (b₂ : Fin m → α)
    (x : Fin n → α) :
    (acc.pushLinear W₂ b₂).eval x = W₂ *ᵥ acc.eval x + b₂ := by -- --- PROOF ---
  cases acc with
  | id => rfl
  | aff W b =>
    simp only [WeightAcc.pushLinear, WeightAcc.eval, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
