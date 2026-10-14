module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# Every member's correction term lies in the float box

`Real.MatExp.corrTerm M r i j k` is `(corrCoeff i · r^i/i!) · (Mⁱ) j k`. The
scalar is in `[κ · r^i/i!, 0]`: `κ ≤ corrCoeff i ≤ 0` and `0 ≤ r^i/i!` below the
stored upper end, so the float lower end, a product of a nonpositive and a
nonnegative bound, only decreases. `smul_outer` and `matPow_outer` finish.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.corrTerm_mem_intervalCorrTerm (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) {i : ℕ} (hi : 2 ≤ i) {M : Mat ℝ n n} (hM : M ∈ A.construct)
    (j k : Fin n) :
    toReal ((MatExp.intervalCorrTerm A r i).inf j k) ≤ Real.MatExp.corrTerm M (toReal r) i j k
      ∧ Real.MatExp.corrTerm M (toReal r) i j k
        ≤ toReal ((MatExp.intervalCorrTerm A r i).sup j k) := by -- --- PROOF ---
  obtain ⟨-, hhi⟩ := MatExp.taylorCoeffBounds_mem hr i
  set ρ := toReal r ^ i / (Nat.factorial i : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  have hκ := MatExp.corrCoeffLow_le (𝕋 := 𝕋) hi
  -- `corrCoeff i ≤ 0`: the bound `corrCoeff_le_sub` at `s = 0`
  have hc0 : Real.MatExp.corrCoeff i ≤ 0 := by
    have h := Real.MatExp.corrCoeff_le_sub hi (le_refl (0:ℝ))
    rwa [zero_pow (by omega : i ≠ 0), sub_zero] at h
  have hlo : toReal (mulDown (MatExp.corrCoeffLow (𝕋 := 𝕋) i) (MatExp.taylorCoeffBounds r i).sup)
      ≤ Real.MatExp.corrCoeff i * ρ :=
    le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonpos_left hhi (le_trans hκ hc0))
      (mul_le_mul_of_nonneg_right hκ hρ))
  have hhi' : Real.MatExp.corrCoeff i * ρ ≤ toReal (zero : 𝕋) := by
    rw [toReal_zero]; exact mul_nonpos_of_nonpos_of_nonneg hc0 hρ
  have hmem := Real.Interval.mem_mat_iff.mp
    (Interval.smul_outer hlo hhi' _ (Interval.matPow_outer A hM i)) j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat, Matrix.smul_apply,
    smul_eq_mul] at hmem
  have heq : Real.MatExp.corrTerm M (toReal r) i j k
      = Real.MatExp.corrCoeff i * ρ * (M ^ i) j k := by
    rw [Real.MatExp.corrTerm]; ring
  rw [heq, MatExp.intervalCorrTerm, Interval.materialiseMat_eq]
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
