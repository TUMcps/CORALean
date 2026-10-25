module

public import CORALean.ContDynamics.LinearSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The float remainder interval holds the zero matrix

`[-E(r)·r, E(r)·r]` in every entry, with `E(r) ≥ 0` at an admissible order, so
`0` is a member: the exact interval holds it (`expRemainderBound_nonneg`), and
the float one holds the exact one (`inputRemainder_subset_intervalInputRemainder`).
What lets `[E(r)·r] U` be bounded from above through the zero matrix, and its
error box bracket `0`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order

## Hypotheses
* `hr` – step length nonnegative
* `hη` – order admissible

## Conclusion
* the zero matrix lies in the float remainder interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The zero matrix lies in the float remainder interval, at `r ≥ 0` and an admissible order. -/
theorem LinearSys.zero_mem_intervalInputRemainder (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) {η : ℕ} (hη : sys.IsOrderAdmissibleFloat r r η) : -- --- CONCL ---
    (0 : Mat ℝ n n) ∈
      (MatExp.intervalInputRemainder (Interval.point sys.A) r η).construct := by -- --- PROOF ---
  have hA : Scalar.toRealMat sys.A ∈ (Interval.point sys.A).construct := Interval.mem_point sys.A
  have hε : ‖toReal r • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) ≤ 1 / 2 :=
    le_trans (by gcongr; exact MatExp.norm_smul_le_normUpperBound _ r hA) hη.2
  have h0 := Real.MatExp.expRemainderBound_nonneg η hε
  -- the exact interval `[-rE, rE]` holds `0`, and the float one holds the exact one
  refine MatExp.inputRemainder_subset_intervalInputRemainder _ hr η hη.2 hA ?_
  refine Real.Interval.mem_mat_iff.mpr fun _ _ => ⟨?_, ?_⟩
  · show -(toReal r * _) ≤ 0
    exact neg_nonpos.mpr (mul_nonneg hr h0)
  · show 0 ≤ toReal r * _
    exact mul_nonneg hr h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
