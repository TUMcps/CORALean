module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# The interpolation error of every member lies in the box's correction matrix

[1, Thm. 3]: `expDiff_mem_correctionMatrix` at a matrix drawn from an interval matrix rather than
at the one the system stores. The point statement is not weakened: it is applied at the member
`M` and read off entrywise, `min` and `max` being monotone, so the finite orders widen from
`corrTerm M` to what `intervalCorrTerm` spans and the tail from the bound at `r • M` to the one
at the dominating matrix of `r • A`. **`hε` is stated at the box, not at `M`**, as in
`ExpIntervalEnclosure`: it has to be checkable from the interval matrix alone, and
`norm_le_absMax` turns it into the condition the point theorem needs.

## Inputs
* `A` – interval matrix
* `r` – step length
* `m` – Taylor order offset
* `M` – member matrix
* `t` – time

## Hypotheses
* `hr` – step length positive
* `hε` – dominating norm small enough for the Taylor order
* `hM` – member lies in the interval matrix
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the member's interpolation error lies in the box's correction matrix

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Althoff's `F` at an interval matrix contains the interpolation error of
every matrix the box holds, at every time of the step. -/
theorem MatExp.expDiff_mem_intervalCorrectionMatrix (A : Interval (Mat ℝ n n)) {r : ℝ}
    (hr : 0 < r) {m : ℕ}
    (hε : ‖(Interval.smul r A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    exp (t • M) - 1 - (t / r) • (exp (r • M) - 1)
      ∈ (MatExp.intervalCorrectionMatrix A r (m + 2)).construct := by -- --- PROOF ---
  have hnorm : ‖r • M‖ ≤ ‖(Interval.smul r A).absMax‖ :=
    Interval.norm_le_absMax (Interval.smul_outer r A hM)
  have hεM : ‖r • M‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (by gcongr) hε
  -- the point statement, at the member, is what everything below only widens
  have hpoint := MatExp.expDiff_mem_correctionMatrix M hr hεM ht0 htr
  have htail : MatExp.expRemainderBound (r • M) (m + 2)
      ≤ MatExp.expRemainderBound (Interval.smul r A).absMax (m + 2) :=
    MatExp.expRemainderBound_mono (m + 2) hnorm hε
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have hpk := Interval.mem_mat_iff.mp hpoint j k
  -- each kept order of the member sits inside the order the box spans
  have hterm : ∀ i ∈ Finset.range (m + 2 - 1),
      (MatExp.intervalCorrTerm A r (i + 2)).inf j k ≤ MatExp.corrTerm M r (i + 2) j k
        ∧ MatExp.corrTerm M r (i + 2) j k
            ≤ (MatExp.intervalCorrTerm A r (i + 2)).sup j k := by
    intro i _
    have hs := Interval.smul_outer
      (MatExp.corrCoeff (i + 2) * r ^ (i + 2) * ((Nat.factorial (i + 2) : ℝ))⁻¹)
      (A.matPow (i + 2)) (Interval.matPow_outer A hM (i + 2))
    have h := Interval.mem_mat_iff.mp hs j k
    have hval : ((MatExp.corrCoeff (i + 2) * r ^ (i + 2)
        * ((Nat.factorial (i + 2) : ℝ))⁻¹) • M ^ (i + 2)) j k
          = MatExp.corrTerm M r (i + 2) j k := by
      simp only [Matrix.smul_apply, smul_eq_mul, MatExp.corrTerm]
      ring
    rw [hval] at h
    exact h
  -- `min` and `max` are monotone, so the comparison survives the sum
  have hlow : ∑ i ∈ Finset.range (m + 2 - 1),
        min ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) 0
      ≤ ∑ i ∈ Finset.range (m + 2 - 1), min (MatExp.corrTerm M r (i + 2) j k) 0 :=
    Finset.sum_le_sum fun i hi => min_le_min (hterm i hi).1 (le_refl 0)
  have hupp : ∑ i ∈ Finset.range (m + 2 - 1), max (MatExp.corrTerm M r (i + 2) j k) 0
      ≤ ∑ i ∈ Finset.range (m + 2 - 1),
          max ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) 0 :=
    Finset.sum_le_sum fun i hi => max_le_max (hterm i hi).2 (le_refl 0)
  simp only [MatExp.correctionMatrix] at hpk
  simp only [MatExp.intervalCorrectionMatrix]
  exact ⟨by linarith [hpk.1], by linarith [hpk.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
