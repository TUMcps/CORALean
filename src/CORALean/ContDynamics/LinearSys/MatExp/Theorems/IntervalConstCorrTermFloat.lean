module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# Every member's integrated correction term lies in the float box

`Real.MatExp.constCorrTerm M r i j k` is `(corrCoeff (i+2) · r^{i+2}/(i+2)!) · (M^{i+1}) j k`.
The scalar is in `[κ · r^{i+2}/(i+2)!, 0]`, by the same two bounds `intervalCorrTerm` uses
one order up: `κ ≤ corrCoeff (i+2) ≤ 0` and `r^{i+2}/(i+2)!` is nonnegative and below the
stored upper end. `smul_outer` and `matPow_outer` finish.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.constCorrTerm_mem_intervalConstCorrTerm (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) (i : ℕ) {M : Mat ℝ n n} (hM : M ∈ A.construct) (j k : Fin n) :
    toReal ((MatExp.intervalConstCorrTerm A r i).inf j k)
        ≤ Real.MatExp.constCorrTerm M (toReal r) i j k
      ∧ Real.MatExp.constCorrTerm M (toReal r) i j k
        ≤ toReal ((MatExp.intervalConstCorrTerm A r i).sup j k) := by -- --- PROOF ---
  obtain ⟨-, hhi⟩ := MatExp.taylorCoeffBounds_mem hr (i + 2)
  set ρ := toReal r ^ (i + 2) / (Nat.factorial (i + 2) : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  have hκ := MatExp.corrCoeffLow_le (𝕋 := 𝕋) (show 2 ≤ i + 2 by omega)
  have hc0 : Real.MatExp.corrCoeff (i + 2) ≤ 0 := by
    have h := Real.MatExp.corrCoeff_le_sub (show 2 ≤ i + 2 by omega) (le_refl (0:ℝ))
    rwa [zero_pow (by omega : i + 2 ≠ 0), sub_zero] at h
  -- the lower end: a nonpositive `κ` against the upper end of the nonnegative scalar
  have hlo : toReal (mulDown (MatExp.corrCoeffLow (𝕋 := 𝕋) (i + 2))
        (MatExp.taylorCoeffBounds r (i + 2)).sup)
      ≤ Real.MatExp.corrCoeff (i + 2) * ρ :=
    le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonpos_left hhi (le_trans hκ hc0))
      (mul_le_mul_of_nonneg_right hκ hρ))
  have hhi' : Real.MatExp.corrCoeff (i + 2) * ρ ≤ toReal (zero : 𝕋) := by
    rw [toReal_zero]; exact mul_nonpos_of_nonpos_of_nonneg hc0 hρ
  -- `smul_outer` and `matPow_outer` put the entry in the float box
  have hmem := Real.Interval.mem_mat_iff.mp
    (Interval.smul_outer hlo hhi' _ (Interval.matPow_outer A hM (i + 1))) j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat, Matrix.smul_apply,
    smul_eq_mul] at hmem
  have heq : Real.MatExp.constCorrTerm M (toReal r) i j k
      = Real.MatExp.corrCoeff (i + 2) * ρ * (M ^ (i + 1)) j k := by
    rw [Real.MatExp.constCorrTerm]; ring
  rw [heq, MatExp.intervalConstCorrTerm, Interval.materialiseMat_eq]
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
