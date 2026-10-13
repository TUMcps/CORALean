module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# The remainder bound is non-negative where it is sound

`expRemainderBound x η` is a non-negative power over a factorial, times the inverse of
`1 - ‖x‖ / (η + 2)`, which is positive as soon as `‖x‖ / (η + 2)` is under `1/2`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expRemainderBound_nonneg {x : Mat ℝ n n} (η : ℕ)
    (hε : ‖x‖ / ((η : ℝ) + 2) ≤ 1 / 2) : 0 ≤ MatExp.expRemainderBound x η := by
  have hpos : 0 < 1 - ‖x‖ / ((η : ℝ) + 2) := by linarith
  exact mul_nonneg (by positivity) (inv_nonneg.mpr hpos.le)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
