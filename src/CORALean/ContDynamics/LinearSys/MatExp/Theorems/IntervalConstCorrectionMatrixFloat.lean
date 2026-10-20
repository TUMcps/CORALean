module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrixSubsetFloat

@[expose] public section

/-!
# The integrated interpolation error of every member lies in the float `F̃`

Through the exact point correction: `Real.MatExp.expIntegralDiff_mem_constCorrectionMatrix` at
the member `M` puts it in the exact `G` at `M`, which
`constCorrectionMatrix_subset_intervalConstCorrectionMatrix` puts in the float one. `hε` asks
`1/2`, as the float remainder bound does, where the exact one asks `< 1`. This is the float `G`
of `curvatureEnclosure`: the true object `∫₀ᵗ e^{Mσ}dσ - (t/r)∫₀ʳ e^{Mσ}dσ` of every matrix the
box holds is in it.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `η` – Taylor order
* `M` – member matrix
* `t` – time

## Hypotheses
* `hr` – step length positive
* `hε` – float norm bound small enough for the Taylor order
* `hM` – member lies in the interval matrix
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the member's integrated interpolation error lies in the float integrated correction
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix (A : Interval (Mat 𝕋 n n))
    {r : 𝕋} (hr : 0 < toReal r) (η : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {t : ℝ} (ht0 : 0 ≤ t)
    (htr : t ≤ toReal r) : -- --- CONCL ---
    Real.MatExp.expIntegral M t - (t / toReal r) • Real.MatExp.expIntegral M (toReal r)
      ∈ (MatExp.intervalConstCorrectionMatrix A r η).construct := by -- --- PROOF ---
  have hnorm := MatExp.norm_smul_le_normUpperBound A r hM
  have hden : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hε' : ‖toReal r • M‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm hden.le) hε) (by norm_num)
  -- the exact point statement, at the member, then the exact `G` inside the float one
  exact MatExp.constCorrectionMatrix_subset_intervalConstCorrectionMatrix A hr.le η hε hM
    (Real.MatExp.expIntegralDiff_mem_constCorrectionMatrix M hr η hε' ht0 htr)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
