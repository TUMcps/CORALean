module

public import CORALean.NN.Operations.WeightAccPushAffine
public import CORALean.NN.Operations.WeightAccEval

@[expose] public section

/-!
# Fusing an elementwise affine layer composes the maps

`s ⊙ (W x + b) + o = (diag s W) x + (s ⊙ b + o)`, exactly.
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

/-- The pushed accumulator is the accumulated map followed by `x ↦ s ⊙ x + o`. -/
theorem WeightAcc.pushAffine_eval (acc : WeightAcc α n d) (s o : Fin d → α) (x : Fin n → α) :
    (acc.pushAffine s o).eval x = fun i => s i * acc.eval x i + o i := by -- --- PROOF ---
  cases acc with
  | id => ext i; simp [WeightAcc.pushAffine, WeightAcc.eval, Matrix.mulVec_diagonal]
  | aff W b =>
    ext i
    simp only [WeightAcc.pushAffine, WeightAcc.eval, Pi.add_apply, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_diagonal, mul_add, add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
