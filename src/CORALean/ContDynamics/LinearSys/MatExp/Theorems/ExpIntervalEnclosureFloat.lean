import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryExpSubExpTaylorLeFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormUpperBoundFloat
import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax

/-!
# The matrix exponential lies in its float interval enclosure

Entry by entry, as `Real.MatExp.exp_mem_expIntervalEnclosure` does: `norm_le_
absMax`/`norm_absMax_le_normUpperBound` replace the pointwise tail bound by a
uniform one at `normUpperBound A`, `expRemainderBound_le` rounds that bound to
a float, and `subDown_le_sub`/`add_le_addUp` finish widening the Taylor box.

`hε` asks `1/2`, not `< 1`: `expRemainderBound_le`'s geometric factor is the
fixed constant `2`, sound only under the stronger margin.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.exp_mem_expIntervalEnclosure (A : Interval (Mat 𝕋 n n)) (η : ℕ) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) (hε : toReal (MatExp.normUpperBound A) / ((η : ℝ) + 2) ≤ 1 / 2) :
    exp M ∈ (MatExp.expIntervalEnclosure A η).construct := by -- --- PROOF ---
  refine Real.Interval.mem_mat_iff.mpr fun i j => ?_
  have htay := Real.Interval.mem_mat_iff.mp (MatExp.expTaylor_mem_expIntervalTaylor A hM η) i j
  simp only [Interval.nominal, RealImage.realImage, toRealMat] at htay
  have hb := MatExp.abs_entry_exp_sub_expTaylor_le A η hM hε i j
  rw [abs_le] at hb
  constructor
  · show toReal (subDown ((MatExp.expIntervalTaylor A η).inf i j)
        (MatExp.expRemainderBound (MatExp.normUpperBound A) η)) ≤ exp M i j
    have hsd := subDown_le_sub ((MatExp.expIntervalTaylor A η).inf i j)
      (MatExp.expRemainderBound (MatExp.normUpperBound A) η)
    linarith [hsd, htay.1, hb.1]
  · show exp M i j ≤ toReal (addUp ((MatExp.expIntervalTaylor A η).sup i j)
        (MatExp.expRemainderBound (MatExp.normUpperBound A) η))
    have hau := add_le_addUp ((MatExp.expIntervalTaylor A η).sup i j)
      (MatExp.expRemainderBound (MatExp.normUpperBound A) η)
    linarith [hau, htay.2, hb.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
