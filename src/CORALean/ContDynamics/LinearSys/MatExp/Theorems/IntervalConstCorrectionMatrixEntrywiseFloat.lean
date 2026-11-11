module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# The constant input's interpolation error lies in CORA's float `G`

`Real.MatExp.expIntegralDiff_mem_constCorrectionMatrixEntrywise` at the member `M`, through the
float box: the kept orders by `sum_constCorrTerm_bracket`, the tail by `r` times the stored bound
`W` over `E(r,η)` entry by entry [1].

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `η` – Taylor order
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
* the constant input's interpolation error lies in the float integrated correction matrix

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

/-- Every member's integrated correction term lies in the float box. -/
private theorem MatExp.aux_constCorrTerm_mem_intervalConstCorrTerm (A : Interval (Mat 𝕋 n n))
    {r : 𝕋} (hr : 0 ≤ toReal r) (i : ℕ) {M : Mat ℝ n n} (hM : M ∈ A.toSet)
    (j k : Fin n) : -- --- CONCL ---
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


private theorem MatExp.aux_sum_constCorrTerm_bracket (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) (η : ℕ) {M : Mat ℝ n n} (hM : M ∈ A.toSet) (j k : Fin n) : -- --- CONCL ---
    toReal (sumDown fun i : Fin η =>
        minimum ((MatExp.intervalConstCorrTerm A r i).inf j k) zero)
      ≤ ∑ i ∈ Finset.range η, min (Real.MatExp.constCorrTerm M (toReal r) i j k) 0
    ∧ ∑ i ∈ Finset.range η, max (Real.MatExp.constCorrTerm M (toReal r) i j k) 0
      ≤ toReal (sumUp fun i : Fin η =>
        maximum ((MatExp.intervalConstCorrTerm A r i).sup j k) zero) := by -- --- PROOF ---
  have hterm := fun i : ℕ => MatExp.aux_constCorrTerm_mem_intervalConstCorrTerm A hr i hM j k
  constructor
  · refine le_trans (sumDown_le_sum _) ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i => min (Real.MatExp.constCorrTerm M _ i j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_minimum, toReal_zero]
    exact min_le_min_right _ (hterm i).1
  · refine le_trans ?_ (sum_le_sumUp _)
    rw [← Fin.sum_univ_eq_sum_range (fun i => max (Real.MatExp.constCorrTerm M _ i j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_maximum, toReal_zero]
    exact max_le_max_right _ (hterm i).2


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrixEntrywise
    (A : Interval (Mat 𝕋 n n)) {r : 𝕋} (hr : 0 < toReal r) (η : ℕ) (W : Mat 𝕋 n n)
    {M : Mat ℝ n n} (hM : M ∈ A.toSet)
    (hW : ∀ j k, Real.MatExp.expRemainderMat M (toReal r) η j k ≤ toReal (W j k))
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ toReal r) : -- --- CONCL ---
    Real.MatExp.expIntegral M t - (t / toReal r) • Real.MatExp.expIntegral M (toReal r)
      ∈ (MatExp.intervalConstCorrectionMatrixEntrywise A r η W).toSet := by -- --- PROOF ---
  have hX := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.expIntegralDiff_mem_constCorrectionMatrixEntrywise M hr η ht0 htr)
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX j k
  simp only [Real.MatExp.constCorrectionMatrixEntrywise] at h1 h2
  obtain ⟨hlo, hhi⟩ := MatExp.aux_sum_constCorrTerm_bracket A hr.le η hM j k
  -- the tail `r E(r)` and the rounded sums bracket the exact entry
  have hrE : toReal r * Real.MatExp.expRemainderMat M (toReal r) η j k ≤ toReal (mulUp r (W j k)) :=
    le_trans (mul_le_mul_of_nonneg_left (hW j k) hr.le) (mul_le_mulUp _ _)
  set sLo := sumDown fun i : Fin η =>
    minimum ((MatExp.intervalConstCorrTerm A r i).inf j k) zero
  set sHi := sumUp fun i : Fin η =>
    maximum ((MatExp.intervalConstCorrTerm A r i).sup j k) zero
  simp only [MatExp.intervalConstCorrectionMatrixEntrywise, Interval.materialiseMat_eq,
    Interval.nominal, RealImage.realImage, toRealMat, Fin.getElem_fin, Vector.getElem_ofFn]
  show toReal (subDown sLo (mulUp r (W j k))) ≤ _ ∧ _ ≤ toReal (addUp sHi (mulUp r (W j k)))
  have hsd := subDown_le_sub sLo (mulUp r (W j k))
  have hau := add_le_addUp sHi (mulUp r (W j k))
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
