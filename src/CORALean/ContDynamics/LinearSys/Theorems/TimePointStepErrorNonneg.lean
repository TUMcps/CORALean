import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundNonneg
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError

/-!
# A step's error radius is non-negative

`timePointStepError` is `2 (∑ⱼ absBound j) r` times `e^{r‖A‖} - 1` plus the series remainder:
the reach is a sum of absolute values, `e^x ≥ 1 + x`, and the remainder is non-negative where
its geometric factor is bounded.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.timePointStepError_nonneg (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 ≤ r)
    (η : ℕ) (U : Zonotope (Vec ℝ n)) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) ≤ 1 / 2) :
    0 ≤ sys.timePointStepError r η U := by -- --- PROOF ---
  have hS : 0 ≤ ∑ j, U.absBound j :=
    Finset.sum_nonneg fun j _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ =>
      abs_nonneg _)
  -- the growth term, then the remainder
  have hexp : 0 ≤ Real.exp (r * ‖toRealMat sys.A‖) - 1 := by
    have := Real.add_one_le_exp (r * ‖toRealMat sys.A‖)
    nlinarith [mul_nonneg hr (norm_nonneg (toRealMat sys.A))]
  have hrem := MatExp.expRemainderBound_nonneg η hε
  unfold LinearSys.timePointStepError
  positivity

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
