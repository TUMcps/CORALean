module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MatPowOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeMatIntervalContains

@[expose] public section

/-!
# The interpolation error of every member lies in the float matrix-zonotope correction

`expDiff_mem_intervalCorrectionMatrix` with the orders taken from the matrix
zonotope: `Real.MatExp.expDiff_mem_correctionMatrix` at the member `M` bounds each
entry by sums of `min/max (corrTerm, 0)` widened by `E(r M)`;
`aux_corrTerm_mem_matZonoCorrTerm` puts each order inside the float term, and the
member lies in the zonotope's box (`matInterval_contains`), which is where the
remainder is taken. `hε` asks `1/2`, as the float remainder bound does.

## Inputs
* `Z` – float matrix zonotope
* `r` – float step length
* `m` – Taylor order offset
* `M` – member matrix
* `t` – time

## Hypotheses
* `hr` – step length positive
* `hε` – float norm bound small enough for the Taylor order
* `hM` – member lies in the matrix zonotope
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the member's interpolation error lies in the float matrix-zonotope correction
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every member's correction term lies in the float matrix-zonotope term. -/
theorem MatExp.aux_corrTerm_mem_matZonoCorrTerm (M : Zonotope (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) {i : ℕ} (hi : 2 ≤ i) {A : Mat ℝ n n} (hA : A ∈ M.construct)
    (j k : Fin n) : -- --- CONCL ---
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
  have hlo : toReal (mulDown (MatExp.corrCoeffLow (𝕋 := 𝕋) i) (MatExp.taylorCoeffBounds r i).sup)
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expDiff_mem_matZonoCorrectionMatrix (Z : Zonotope (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 < toReal r) {m : ℕ}
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r Z.matInterval))
      / (((m + 2 : ℕ) : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ Z.construct) {t : ℝ} (ht0 : 0 ≤ t)
    (htr : t ≤ toReal r) : -- --- CONCL ---
    exp (t • M) - 1 - (t / toReal r) • (exp (toReal r • M) - 1)
      ∈ (MatExp.matZonoCorrectionMatrix Z r (m + 2)).construct := by -- --- PROOF ---
  have hnorm := MatExp.norm_smul_le_normUpperBound Z.matInterval r
    (Zonotope.matInterval_contains Z hM)
  have hden : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) + 2 := by positivity
  have hε' : ‖toReal r • M‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm hden.le) hε) (by norm_num)
  have hE := MatExp.expRemainderBound_le (m + 2) hnorm (le_trans (norm_nonneg _) hnorm) hε
  have hX := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.expDiff_mem_correctionMatrix M hr hε' ht0 htr)
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX j k
  simp only [Real.MatExp.correctionMatrix, show m + 2 - 1 = m + 1 from rfl] at h1 h2
  have hterm := fun i : ℕ =>
    MatExp.aux_corrTerm_mem_matZonoCorrTerm Z hr.le (i := i + 2) (by omega) hM j k
  -- the stored orders, rounded and summed, bracket the exact sums
  have hlo : toReal (sumDown fun i : Fin (m + 1) =>
        minimum ((MatExp.matZonoCorrTerm Z r (i + 2)).inf j k) zero)
      ≤ ∑ i ∈ Finset.range (m + 1), min (Real.MatExp.corrTerm M (toReal r) (i + 2) j k) 0 := by
    refine le_trans (sumDown_le_sum _) ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i => min (Real.MatExp.corrTerm M _ (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_minimum, toReal_zero]
    exact min_le_min_right _ (hterm i).1
  have hhi : ∑ i ∈ Finset.range (m + 1), max (Real.MatExp.corrTerm M (toReal r) (i + 2) j k) 0
      ≤ toReal (sumUp fun i : Fin (m + 1) =>
        maximum ((MatExp.matZonoCorrTerm Z r (i + 2)).sup j k) zero) := by
    refine le_trans ?_ (sum_le_sumUp _)
    rw [← Fin.sum_univ_eq_sum_range (fun i => max (Real.MatExp.corrTerm M _ (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_maximum, toReal_zero]
    exact max_le_max_right _ (hterm i).2
  -- the stored entry is the rounded difference and sum of exactly these
  set E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r Z.matInterval))
    (m + 2)
  set sLo := sumDown fun i : Fin (m + 1) =>
    minimum ((MatExp.matZonoCorrTerm Z r (i + 2)).inf j k) zero
  set sHi := sumUp fun i : Fin (m + 1) =>
    maximum ((MatExp.matZonoCorrTerm Z r (i + 2)).sup j k) zero
  simp only [MatExp.matZonoCorrectionMatrix, Interval.materialiseMat_eq, Interval.nominal,
    RealImage.realImage, toRealMat, Fin.getElem_fin, Vector.getElem_ofFn]
  show toReal (subDown sLo E) ≤ _ ∧ _ ≤ toReal (addUp sHi E)
  have hsd := subDown_le_sub sLo E
  have hau := add_le_addUp sHi E
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
