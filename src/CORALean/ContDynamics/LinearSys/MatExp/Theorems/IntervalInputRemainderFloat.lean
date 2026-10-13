import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat

/-!
# Every member's input remainder lies in the float box

The exact `Real.MatExp.inputRemainder M r η` at any member `M`, as a set, sits
inside the float box: its width `r · E(r M)` is below `r` times the float
remainder bound (`expRemainderBound_le` at `norm_smul_le_normUpperBound`),
rounded up. `hε` asks `1/2`, as every float remainder bound does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.inputRemainder_subset_intervalInputRemainder (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) (η : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) :
    (Real.MatExp.inputRemainder M (toReal r) η).construct
      ⊆ (MatExp.intervalInputRemainder A r η).construct := by -- --- PROOF ---
  have hnorm := MatExp.norm_smul_le_normUpperBound A r hM
  have hE := MatExp.expRemainderBound_le η hnorm (le_trans (norm_nonneg _) hnorm) hε
  -- the exact width `r · E(r M)`, below the stored one
  have hw : toReal r * Real.MatExp.expRemainderBound (toReal r • M) η
      ≤ toReal (mulUp r (MatExp.expRemainderBound
          (MatExp.normUpperBound (Interval.smul r r A)) η)) :=
    le_trans (mul_le_mul_of_nonneg_left hE hr) (mul_le_mulUp _ _)
  intro N hN
  have hN' := Real.Interval.mem_mat_iff.mp hN
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  simp only [Real.MatExp.inputRemainder] at hN'
  simp only [MatExp.intervalInputRemainder, Interval.nominal, RealImage.realImage, toRealMat,
    toReal_neg]
  obtain ⟨h1, h2⟩ := hN' j k
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
