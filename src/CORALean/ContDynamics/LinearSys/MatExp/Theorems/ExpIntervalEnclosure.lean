module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax

@[expose] public section

/-!
# The matrix exponential lies in its interval enclosure

[1, Sec. 3.3.1], entry by entry as `exp_mem_expEnclosure` does, with
`norm_le_absMax`/`expRemainderBound_mono` replacing the pointwise tail bound by
a uniform one taken at `A.absMax`.

**`hε` is stated at `A.absMax`, not at `M`**, and has to be: it must be
checkable from the interval matrix alone, before any particular `M` is fixed,
and `norm_le_absMax` is exactly what lets it imply the pointwise condition
`norm_exp_sub_expTaylor_le` needs.

## Inputs
* `A` – interval matrix
* `η` – Taylor order
* `M` – member matrix

## Hypotheses
* `hM` – member lies in the interval matrix
* `hε` – dominating norm small enough for the Taylor order

## Conclusion
* the exponential of the member lies in the interval enclosure

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every entry of the exponential sits between the interval Taylor truncation
and the tail bound taken at the interval matrix's dominating matrix. -/
theorem MatExp.exp_mem_expIntervalEnclosure (A : Interval (Mat ℝ n n)) (η : ℕ)
    {M : Mat ℝ n n} (hM : M ∈ A.construct)
    (hε : ‖A.absMax‖ / ((η : ℝ) + 2) < 1) :
    exp M ∈ (MatExp.expIntervalEnclosure A η).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hnorm : ‖M‖ ≤ ‖A.absMax‖ := Interval.norm_le_absMax hM
  have hfrac : ‖M‖ / ((η : ℝ) + 2) ≤ ‖A.absMax‖ / ((η : ℝ) + 2) := by gcongr
  have hεM : ‖M‖ / ((η : ℝ) + 2) < 1 := lt_of_le_of_lt hfrac hε
  -- the pointwise tail bound at `M`, widened to the uniform one at `A.absMax`
  have h : |exp M i j - MatExp.expTaylor M η i j|
      ≤ MatExp.expRemainderBound A.absMax η := by
    calc |exp M i j - MatExp.expTaylor M η i j|
        = |(exp M - MatExp.expTaylor M η) i j| := by rw [Matrix.sub_apply]
      _ ≤ ‖exp M - MatExp.expTaylor M η‖ := abs_entry_le_norm _ i j
      _ ≤ MatExp.expRemainderBound M η := norm_exp_sub_expTaylor_le M η hεM
      _ ≤ MatExp.expRemainderBound A.absMax η := MatExp.expRemainderBound_mono η hnorm hε
  have htay := Interval.mem_mat_iff.mp (MatExp.expTaylor_mem_expIntervalTaylor A hM η) i j
  rw [abs_le] at h
  constructor
  · show (MatExp.expIntervalTaylor A η).inf i j - MatExp.expRemainderBound A.absMax η
        ≤ exp M i j
    linarith [h.1, htay.1]
  · show exp M i j ≤ (MatExp.expIntervalTaylor A η).sup i j
        + MatExp.expRemainderBound A.absMax η
    linarith [h.2, htay.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
