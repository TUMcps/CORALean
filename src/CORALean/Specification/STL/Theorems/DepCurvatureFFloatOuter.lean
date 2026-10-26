module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.Specification.STL.Operations.DepCurvatureFFloat

@[expose] public section

/-!
# The interval matrix `F` over floats encloses the real one

Each order of `STL.depCurvatureF` [1, Alg. 1] lies inside its float term, the rounded sums bracket
the exact ones, and the remainder: the entry of the matrix `E` is under the scalar bound
(`expRemainderMat_entry_le_bound`), which the float bound holds (`expRemainderBound_le`), so the
float `F` holds the real one at the matrix the stored floats read as.
## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `κ` – Taylor order

## Hypotheses
* `hr` – the time step is nonnegative
* `hε` – the float norm bound is small enough for the Taylor order

## Conclusion
* the real curvature interval lies inside the float one
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.FloatOps Float.SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The correction term of order `i` at the matrix the floats read as lies in the float term. -/
private theorem STL.aux_depCurvatureF_term (A : Mat 𝕋 n n) {r : 𝕋} (hr : 0 ≤ toReal r) {i : ℕ}
    (hi : 2 ≤ i) (j k : Fin n) : -- --- CONCL ---
    toReal ((MatExp.intervalCorrTerm (Interval.point A) r i).inf j k) ≤
        Real.MatExp.corrTerm (toRealMat A) (toReal r) i j k ∧
      Real.MatExp.corrTerm (toRealMat A) (toReal r) i j k ≤
        toReal ((MatExp.intervalCorrTerm (Interval.point A) r i).sup j k) := by -- --- PROOF ---
  have hM : toRealMat A ∈ (Interval.point A).construct := Float.Interval.mem_point A
  obtain ⟨-, hhi⟩ := MatExp.taylorCoeffBounds_mem hr i
  set ρ := toReal r ^ i / (Nat.factorial i : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  have hκ := MatExp.corrCoeffLow_le (𝕋 := 𝕋) hi
  -- `corrCoeff i ≤ 0`
  have hc0 : Real.MatExp.corrCoeff i ≤ 0 := by
    have h := Real.MatExp.corrCoeff_le_sub hi (le_refl (0 : ℝ))
    rwa [zero_pow (by omega : i ≠ 0), sub_zero] at h
  have hlo : toReal (mulDown (MatExp.corrCoeffLow (𝕋 := 𝕋) i) (MatExp.taylorCoeffBounds r i).sup)
      ≤ Real.MatExp.corrCoeff i * ρ :=
    le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonpos_left hhi (le_trans hκ hc0))
      (mul_le_mul_of_nonneg_right hκ hρ))
  have hhi' : Real.MatExp.corrCoeff i * ρ ≤ toReal (zero : 𝕋) := by
    rw [toReal_zero]; exact mul_nonpos_of_nonpos_of_nonneg hc0 hρ
  have hmem := Real.Interval.mem_mat_iff.mp
    (Interval.smul_outer hlo hhi' _ (Interval.matPow_outer (Interval.point A) hM i)) j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat, Matrix.smul_apply,
    smul_eq_mul] at hmem
  have heq : Real.MatExp.corrTerm (toRealMat A) (toReal r) i j k
      = Real.MatExp.corrCoeff i * ρ * ((toRealMat A) ^ i) j k := by
    rw [Real.MatExp.corrTerm]; ring
  rw [heq, MatExp.intervalCorrTerm, Interval.materialiseMat_eq]
  exact hmem


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float `F` holds the real `F` of the matrix the stored floats read as. -/
theorem STL.depCurvatureFFloat_outer (A : Mat 𝕋 n n) {Δt : 𝕋} (hr : 0 ≤ toReal Δt) (κ : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((κ : ℝ) + 2) ≤ 1 / 2) : -- --- CONCL ---
    (STL.depCurvatureF (toRealMat A) (toReal Δt) κ).construct ⊆
      (STL.depCurvatureFFloat A Δt κ).construct := by -- --- PROOF ---
  have hM : toRealMat A ∈ (Interval.point A).construct := Float.Interval.mem_point A
  have hnorm := MatExp.norm_smul_le_normUpperBound (Interval.point A) Δt hM
  -- the scaled matrix has a norm under the bound the Taylor order admits
  have hlt : ‖toReal Δt • toRealMat A‖ / ((κ : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm (by positivity)) hε)
      (by norm_num)
  have hE := MatExp.expRemainderBound_le κ hnorm (le_trans (norm_nonneg _) hnorm) hε
  intro X hX
  have hX' := Real.Interval.mem_mat_iff.mp hX
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX' j k
  simp only [STL.depCurvatureF] at h1 h2
  -- the entry of the remainder matrix is under the float scalar bound
  have hEjk := ((le_abs_self _).trans
    (Real.MatExp.expRemainderMat_entry_le_bound (toRealMat A) κ hlt j k)).trans hE
  have hterm := fun i : ℕ => STL.aux_depCurvatureF_term A hr (i := i + 2) (by omega) j k
  -- the stored orders, rounded and summed, bracket the exact sums
  have hlo : toReal (sumDown fun i : Fin (κ - 1) =>
        minimum ((MatExp.intervalCorrTerm (Interval.point A) Δt (i + 2)).inf j k) zero)
      ≤ ∑ i ∈ Finset.range (κ - 1), min
        (Real.MatExp.corrTerm (toRealMat A) (toReal Δt) (i + 2) j k) 0 := by
    refine le_trans (sumDown_le_sum _) ?_
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => min (Real.MatExp.corrTerm (toRealMat A) (toReal Δt) (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_minimum, toReal_zero]
    exact min_le_min_right _ (hterm i).1
  have hhi : ∑ i ∈ Finset.range (κ - 1), max
        (Real.MatExp.corrTerm (toRealMat A) (toReal Δt) (i + 2) j k) 0
      ≤ toReal (sumUp fun i : Fin (κ - 1) =>
        maximum ((MatExp.intervalCorrTerm (Interval.point A) Δt (i + 2)).sup j k) zero) := by
    refine le_trans ?_ (sum_le_sumUp _)
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => max (Real.MatExp.corrTerm (toRealMat A) (toReal Δt) (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_maximum, toReal_zero]
    exact max_le_max_right _ (hterm i).2
  -- the stored entry is the rounded difference and sum of exactly these
  set E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul Δt Δt
    (Interval.point A))) κ
  set sLo := sumDown fun i : Fin (κ - 1) =>
    minimum ((MatExp.intervalCorrTerm (Interval.point A) Δt (i + 2)).inf j k) zero
  set sHi := sumUp fun i : Fin (κ - 1) =>
    maximum ((MatExp.intervalCorrTerm (Interval.point A) Δt (i + 2)).sup j k) zero
  simp only [STL.depCurvatureFFloat, MatExp.intervalCorrectionMatrix, Interval.materialiseMat_eq,
    Fin.getElem_fin, Vector.getElem_ofFn]
  show toReal (subDown sLo E) ≤ _ ∧ _ ≤ toReal (addUp sHi E)
  have hsd := subDown_le_sub sLo E
  have hau := add_le_addUp sHi E
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
