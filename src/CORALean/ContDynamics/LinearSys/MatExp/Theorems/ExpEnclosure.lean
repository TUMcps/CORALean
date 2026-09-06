import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
import CORALean.ContSet.Interval.Real.Theorems.MemMat

/-!
# The matrix exponential lies in its enclosure

[1, Eq. (3.2)–(3.3)], assembled entrywise: `norm_exp_sub_expTaylor_le` bounds
the whole matrix, and an entry of a bounded matrix is bounded by the same
amount, so the truncation plus the remainder brackets every entry of `exp x`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every entry of the exponential sits between the truncation and the tail bound. -/
theorem MatExp.exp_mem_expEnclosure (x : Mat ℝ n n) (η : ℕ)
    (hε : ‖x‖ / ((η : ℝ) + 2) < 1) :
    exp x ∈ (MatExp.expEnclosure x η).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have h : |exp x i j - MatExp.expTaylor x η i j|
      ≤ MatExp.expRemainderBound x η := by
    calc |exp x i j - MatExp.expTaylor x η i j|
        = |(exp x - MatExp.expTaylor x η) i j| := by rw [Matrix.sub_apply]
      _ ≤ ‖exp x - MatExp.expTaylor x η‖ := abs_entry_le_norm _ i j
      _ ≤ MatExp.expRemainderBound x η := norm_exp_sub_expTaylor_le x η hε
  rw [abs_le] at h
  constructor
  · show MatExp.expTaylor x η i j - MatExp.expRemainderBound x η ≤ exp x i j
    linarith [h.1]
  · show exp x i j ≤ MatExp.expTaylor x η i j + MatExp.expRemainderBound x η
    linarith [h.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
