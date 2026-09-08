import CORALean.ContDynamics.LinearSys.MatExp.ExpRemainderStep
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMulExpRemainderBoundLt

/-!
# The chosen step meets the error it was chosen for

What turns `exists_mul_expRemainderBound_lt` into a rule: `expRemainderStep` is
admissible whenever the error is, so a caller states `ε` and gets a positive
step, the bound and the side condition together.

No minimality counterpart: the admissible steps are an interval open at `0` and
so have no least element. What a tuning algorithm wants of a step is the
largest admissible one, and nothing here says the chosen one is that.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open scoped Classical in
/-- The step chosen for `ε` at order `η` is admissible for it: positive, under
the bound, and sound. -/
theorem MatExp.expRemainderStep_spec (A : Mat ℝ n n) (η : ℕ) {ε : ℝ} (hε : 0 < ε) :
    MatExp.StepAdmissible A η ε (MatExp.expRemainderStep A η ε) := by -- --- PROOF ---
  obtain ⟨r, hr0, hrb, hrs⟩ := MatExp.exists_mul_expRemainderBound_lt A η hε
  have h : ∃ r : ℝ, MatExp.StepAdmissible A η ε r := ⟨r, hr0, hrb, hrs⟩
  -- the definition takes its `then` branch, and `Exists.choose_spec` is the claim
  simp only [MatExp.expRemainderStep, dif_pos h]
  exact h.choose_spec

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
