module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrixSubsetFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.Specification.STL.Operations.DepCurvatureGFloat

@[expose] public section

/-!
# The interval matrix `G` over floats encloses the real one

The entries of `STL.depCurvatureG` [1, Alg. 1] are the orders of the constant correction up to `κ`
and the remainder `Δt E` with `E` the entry of the remainder matrix, which is under the scalar bound
(`expRemainderMat_entry_le_bound`), so the real `G` lies inside `constCorrectionMatrix`, which the
float `G` encloses at the matrix the stored floats read as (`constCorrectionMatrix_subset_
intervalConstCorrectionMatrix`).
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float `G` holds the real `G` of the matrix the stored floats read as. -/
theorem STL.depCurvatureGFloat_outer (A : Mat 𝕋 n n) {Δt : 𝕋} (hr : 0 ≤ toReal Δt) (κ : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((κ : ℝ) + 2) ≤ 1 / 2) : -- --- CONCL ---
    (STL.depCurvatureG (toRealMat A) (toReal Δt) κ).construct ⊆
      (STL.depCurvatureGFloat A Δt κ).construct := by -- --- PROOF ---
  have hM : toRealMat A ∈ (Interval.point A).construct := Float.Interval.mem_point A
  have hnorm := MatExp.norm_smul_le_normUpperBound (Interval.point A) Δt hM
  -- the scaled matrix has a norm under the bound the Taylor order admits
  have hlt : ‖toReal Δt • toRealMat A‖ / ((κ : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm (by positivity)) hε)
      (by norm_num)
  -- the real `G` lies inside the constant correction matrix, as `E Δt` is under `Δt` times it
  refine Set.Subset.trans (fun X hX => ?_)
    (MatExp.constCorrectionMatrix_subset_intervalConstCorrectionMatrix (Interval.point A) hr κ
      hε hM)
  have hX' := Real.Interval.mem_mat_iff.mp hX
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX' j k
  simp only [STL.depCurvatureG, Real.MatExp.constCorrectionMatrix] at h1 h2 ⊢
  have hE := mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (Real.MatExp.expRemainderMat_entry_le_bound (toRealMat A) κ hlt j k)) hr
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
