import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

/-!
# An admissible step size

`StepAdmissible`: [1]'s admissibility spec for the step size: a step meeting the admissible
error `ε` at order `η`, positive, its contribution under `ε`, and the side condition at the
scaled matrix.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A step meeting the admissible error `ε` at order `η`: positive, its
contribution under `ε`, and the side condition at the scaled matrix. -/
def MatExp.StepAdmissible (A : Mat ℝ n n) (η : ℕ) (ε : ℝ) (r : ℝ) : Prop :=
  0 < r ∧ r * MatExp.expRemainderBound (r • A) η < ε ∧ ‖r • A‖ / ((η : ℝ) + 2) < 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
