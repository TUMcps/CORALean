import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# `expRemainderBound` is monotone in `‖A‖`

Needed because a step's enclosure is built once, at one norm, and then has to
bound the same tail at every point of a whole step: as long as the norm
elsewhere in the step does not exceed the one the bound was computed at, the
bound taken there still covers it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- Monotone in the norm of its argument, which is what lets one bound taken at
the end of a step stand for every time inside it. -/
theorem MatExp.expRemainderBound_mono {x y : Mat ℝ n n} (η : ℕ) (hxy : ‖x‖ ≤ ‖y‖)
    (hy : ‖y‖ / ((η : ℝ) + 2) < 1) :
    MatExp.expRemainderBound x η ≤ MatExp.expRemainderBound y η := by
  have h2 : (0:ℝ) < (η : ℝ) + 2 := by positivity
  have hfrac : ‖x‖ / ((η : ℝ) + 2) ≤ ‖y‖ / ((η : ℝ) + 2) := by gcongr
  have hdy : 0 < 1 - ‖y‖ / ((η : ℝ) + 2) := by linarith
  have hdx : 0 < 1 - ‖x‖ / ((η : ℝ) + 2) := by linarith
  have hnum : ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
      ≤ ‖y‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by gcongr
  have hinv : (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ ≤ (1 - ‖y‖ / ((η : ℝ) + 2))⁻¹ :=
    inv_anti₀ hdy (by linarith)
  exact mul_le_mul hnum hinv (inv_nonneg.mpr hdx.le) (by positivity)

end CORALean.Real
