module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# An admissible step size

`IsStepAdmissible`: [1]'s admissibility spec for the step size: a step meeting the admissible
error `ε` at order `η`, positive, its contribution under `ε`, and the side condition at the
scaled matrix.

## Inputs
* `A` – system matrix
* `η` – Taylor order
* `ε` – admissible error
* `r` – step length

## Output
* proposition that the step is admissible at the order and error

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A step meeting the admissible error `ε` at order `η`: positive, its
contribution under `ε`, and the side condition at the scaled matrix. -/
def MatExp.IsStepAdmissible (A : Mat ℝ n n) (η : ℕ) (ε : ℝ) (r : ℝ) : Prop :=
  0 < r ∧ r * MatExp.expRemainderBound (r • A) η < ε ∧ ‖r • A‖ / ((η : ℝ) + 2) < 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
