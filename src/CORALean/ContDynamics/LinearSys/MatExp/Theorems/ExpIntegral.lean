import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableNormExpIntegral

/-!
# The integrated exponential series converges

`summable_norm_expIntegral` dominates it by `|t|` times the exponential's own
series; completeness of the matrix algebra turns that absolute bound into
summability outright, which is all the containment theorems downstream need.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- And so summable in the matrix algebra, which is complete. -/
theorem MatExp.summable_expIntegral (A : Mat ℝ n n) (t : ℝ) :
    Summable (fun i : ℕ => (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i) :=
  (MatExp.summable_norm_expIntegral A t).of_norm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
