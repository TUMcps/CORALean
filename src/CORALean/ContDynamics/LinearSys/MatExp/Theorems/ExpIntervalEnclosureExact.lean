module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureExact
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorExact
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

/-!
# The matrix exponential lies in the sharper interval enclosure

[1, Thm. 1]. Entry by entry as `exp_mem_expIntervalEnclosure` does, and with
the same tail bound: only the center differs, `expIntervalTaylorExact` having
orders one and two exactly where the other has them by interval arithmetic.

`hε` is stated at `(t • A).absMax`, not at `t • M`, for the same reason it is
there: it must be checkable from the interval matrix alone, and
`norm_le_absMax` is what turns it into the pointwise condition the tail bound
needs.

## Inputs
* `A` – interval matrix
* `t` – time
* `M` – member matrix
* `κ` – Taylor order

## Hypotheses
* `hM` – member lies in the interval matrix
* `hκ` – order at least two
* `hε` – dominating norm small enough for the Taylor order

## Conclusion
* the exponential of the scaled member lies in the sharper enclosure

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{At}` of every member of the box sits in `⌈e^{At}_κ⌉`. -/
theorem MatExp.exp_mem_expIntervalEnclosureExact (A : Interval (Mat ℝ n n)) (t : ℝ)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {κ : ℕ} (hκ : 2 ≤ κ)
    (hε : ‖(Interval.smul t A).absMax‖ / ((κ : ℝ) + 2) < 1) : -- --- CONCL ---
    exp (t • M) ∈ (MatExp.expIntervalEnclosureExact A t κ).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hMB : t • M ∈ (Interval.smul t A).construct := Interval.smul_outer t A hM
  have hnorm : ‖t • M‖ ≤ ‖(Interval.smul t A).absMax‖ := Interval.norm_le_absMax hMB
  have hfrac : ‖t • M‖ / ((κ : ℝ) + 2)
      ≤ ‖(Interval.smul t A).absMax‖ / ((κ : ℝ) + 2) := by gcongr
  have hεM : ‖t • M‖ / ((κ : ℝ) + 2) < 1 := lt_of_le_of_lt hfrac hε
  -- the pointwise tail bound at `t • M`, widened to the uniform one at the box
  have h : |exp (t • M) i j - MatExp.expTaylor (t • M) κ i j|
      ≤ MatExp.expRemainderBound (Interval.smul t A).absMax κ := by
    calc |exp (t • M) i j - MatExp.expTaylor (t • M) κ i j|
        = |(exp (t • M) - MatExp.expTaylor (t • M) κ) i j| := by rw [Matrix.sub_apply]
      _ ≤ ‖exp (t • M) - MatExp.expTaylor (t • M) κ‖ := abs_entry_le_norm _ i j
      _ ≤ MatExp.expRemainderBound (t • M) κ := norm_exp_sub_expTaylor_le _ κ hεM
      _ ≤ MatExp.expRemainderBound (Interval.smul t A).absMax κ :=
          MatExp.expRemainderBound_mono κ hnorm hε
  have htay := Interval.mem_mat_iff.mp
    (MatExp.expTaylor_mem_expIntervalTaylorExact A t hM hκ) i j
  rw [abs_le] at h
  constructor
  · show (MatExp.expIntervalTaylorExact A t κ).inf i j
        - MatExp.expRemainderBound (Interval.smul t A).absMax κ ≤ exp (t • M) i j
    linarith [h.1, htay.1]
  · show exp (t • M) i j ≤ (MatExp.expIntervalTaylorExact A t κ).sup i j
        + MatExp.expRemainderBound (Interval.smul t A).absMax κ
    linarith [h.2, htay.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
