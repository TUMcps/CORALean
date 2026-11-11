module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# The interpolation error of every member lies in CORA's float correction

`Real.MatExp.expDiff_mem_correctionMatrixEntrywise` at the member `M`, through the float box: the
kept orders by `sum_corrTerm_bracket`, the tail by the stored bound `W` over `E(r,η)` entry by
entry [1]. Nothing is asked of the order: the bound `W` carries whatever the enclosure of
`e^{|A|r}` needs.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `m` – Taylor order offset
* `W` – float bound on the entrywise remainder
* `M` – member matrix
* `t` – time

## Hypotheses
* `hr` – step length positive
* `hM` – member lies in the interval matrix
* `hW` – the bound holds the exact remainder
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the member's interpolation error lies in the float correction matrix

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every member's correction term lies in the float box. -/
private theorem MatExp.aux_corrTerm_mem_intervalCorrTerm (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) {i : ℕ} (hi : 2 ≤ i) {M : Mat ℝ n n} (hM : M ∈ A.toSet)
    (j k : Fin n) : -- --- CONCL ---
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


private theorem MatExp.aux_sum_corrTerm_bracket (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) (m : ℕ) {M : Mat ℝ n n} (hM : M ∈ A.toSet) (j k : Fin n) : -- --- CONCL ---
    toReal (sumDown fun i : Fin (m + 1) =>
        minimum ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) zero)
      ≤ ∑ i ∈ Finset.range (m + 1), min (Real.MatExp.corrTerm M (toReal r) (i + 2) j k) 0
    ∧ ∑ i ∈ Finset.range (m + 1), max (Real.MatExp.corrTerm M (toReal r) (i + 2) j k) 0
      ≤ toReal (sumUp fun i : Fin (m + 1) =>
        maximum ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) zero) := by -- --- PROOF ---
  have hterm := fun i : ℕ =>
    MatExp.aux_corrTerm_mem_intervalCorrTerm A hr (i := i + 2) (by omega) hM j k
  constructor
  · refine le_trans (sumDown_le_sum _) ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i => min (Real.MatExp.corrTerm M _ (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_minimum, toReal_zero]
    exact min_le_min_right _ (hterm i).1
  · refine le_trans ?_ (sum_le_sumUp _)
    rw [← Fin.sum_univ_eq_sum_range (fun i => max (Real.MatExp.corrTerm M _ (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_maximum, toReal_zero]
    exact max_le_max_right _ (hterm i).2


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expDiff_mem_intervalCorrectionMatrixEntrywise (A : Interval (Mat 𝕋 n n))
    {r : 𝕋} (hr : 0 < toReal r) {m : ℕ} (W : Mat 𝕋 n n) {M : Mat ℝ n n} (hM : M ∈ A.toSet)
    (hW : ∀ j k, Real.MatExp.expRemainderMat M (toReal r) (m + 2) j k ≤ toReal (W j k))
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ toReal r) : -- --- CONCL ---
    exp (t • M) - 1 - (t / toReal r) • (exp (toReal r • M) - 1)
      ∈ (MatExp.intervalCorrectionMatrixEntrywise A r (m + 2) W).toSet := by -- --- PROOF ---
  have hX := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.expDiff_mem_correctionMatrixEntrywise M hr (m := m) ht0 htr)
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX j k
  simp only [Real.MatExp.correctionMatrixEntrywise, show m + 2 - 1 = m + 1 from rfl] at h1 h2
  obtain ⟨hlo, hhi⟩ := MatExp.aux_sum_corrTerm_bracket A hr.le m hM j k
  -- the stored entry is the rounded difference and sum of exactly these
  set sLo := sumDown fun i : Fin (m + 1) =>
    minimum ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) zero
  set sHi := sumUp fun i : Fin (m + 1) =>
    maximum ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) zero
  simp only [MatExp.intervalCorrectionMatrixEntrywise, Interval.materialiseMat_eq,
    Interval.nominal, RealImage.realImage, toRealMat, Fin.getElem_fin, Vector.getElem_ofFn]
  show toReal (subDown sLo (W j k)) ≤ _ ∧ _ ≤ toReal (addUp sHi (W j k))
  have hsd := subDown_le_sub sLo (W j k)
  have hau := add_le_addUp sHi (W j k)
  have hWjk := hW j k
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
