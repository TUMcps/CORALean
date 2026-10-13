import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MatPowOuter

/-!
# Every member's correction term lies in the float matrix-zonotope term

`corrTerm_mem_intervalCorrTerm` with the box of the power taken from the matrix
zonotope: a member's `i`-th power lies in the zonotope's `i`-th power
(`matPow_outer`), hence in its box (`matInterval_contains`), and the scalar
`corrCoeff i · r^i/i!` in `[κ·r^i/i!, 0]` scales the box over it.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.corrTerm_mem_matZonoCorrTerm (M : Zonotope (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) {i : ℕ} (hi : 2 ≤ i) {A : Mat ℝ n n} (hA : A ∈ M.construct)
    (j k : Fin n) :
    toReal ((MatExp.matZonoCorrTerm M r i).inf j k) ≤ Real.MatExp.corrTerm A (toReal r) i j k
      ∧ Real.MatExp.corrTerm A (toReal r) i j k
        ≤ toReal ((MatExp.matZonoCorrTerm M r i).sup j k) := by -- --- PROOF ---
  obtain ⟨-, hhi⟩ := MatExp.taylorCoeffBounds_mem hr i
  set ρ := toReal r ^ i / (Nat.factorial i : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  have hκ := MatExp.corrCoeffLow_le (𝕋 := 𝕋) hi
  -- `corrCoeff i ≤ 0`: the bound `corrCoeff_le_sub` at `s = 0`
  have hc0 : Real.MatExp.corrCoeff i ≤ 0 := by
    have h := Real.MatExp.corrCoeff_le_sub hi (le_refl (0:ℝ))
    rwa [zero_pow (by omega : i ≠ 0), sub_zero] at h
  have hlo : toReal (mulDown (MatExp.corrCoeffLow (𝕋 := 𝕋) i) (MatExp.taylorCoeffBounds r i).2)
      ≤ Real.MatExp.corrCoeff i * ρ :=
    le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonpos_left hhi (le_trans hκ hc0))
      (mul_le_mul_of_nonneg_right hκ hρ))
  have hhi' : Real.MatExp.corrCoeff i * ρ ≤ toReal (zero : 𝕋) := by
    rw [toReal_zero]; exact mul_nonpos_of_nonpos_of_nonneg hc0 hρ
  -- the member's power, in the power's box
  have hpow : A ^ i ∈ (M.matPow i).matInterval.construct :=
    Zonotope.matInterval_contains _ (Zonotope.matPow_outer M hA i)
  have hmem := Real.Interval.mem_mat_iff.mp (Interval.smul_outer hlo hhi' _ hpow) j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat, Matrix.smul_apply,
    smul_eq_mul] at hmem
  have heq : Real.MatExp.corrTerm A (toReal r) i j k
      = Real.MatExp.corrCoeff i * ρ * (A ^ i) j k := by
    rw [Real.MatExp.corrTerm]; ring
  rw [heq, MatExp.matZonoCorrTerm, Interval.materialiseMat_eq]
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
