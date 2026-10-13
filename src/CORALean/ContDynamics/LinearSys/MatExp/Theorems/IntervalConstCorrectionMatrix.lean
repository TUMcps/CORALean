module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# Every member's constant-input interpolation error lies in the box's `F̃`

Althoff's `F̃` of [1, Prop. 3.4] at an interval matrix rather than at the one
the system stores: `ConstCorrectionMatrix` one step over, following
`IntervalCorrectionMatrix`'s own pattern — apply the point theorem at a member
`M`, then read the finite orders off entrywise through `intervalConstCorrTerm`'s
`min`/`max` monotonicity and the tail through `expRemainderBound_mono`, both
scaled by `r` as `constCorrectionMatrix` itself is.

**`hε` is stated at the box, not at `M`**, exactly as in
`IntervalCorrectionMatrix`, so it is checkable before a member is fixed;
`norm_le_absMax` turns it into the condition the point theorem needs.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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

/-- Althoff's `F̃` at an interval matrix contains the constant input's
interpolation error, at every time of the step, of every matrix the box holds. -/
theorem MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix (A : Interval (Mat ℝ n n))
    {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖(Interval.smul r A).absMax‖ / ((η : ℝ) + 2) < 1)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    MatExp.expIntegral M t - (t / r) • MatExp.expIntegral M r
      ∈ (MatExp.intervalConstCorrectionMatrix A r η).construct := by -- --- PROOF ---
  have hnorm : ‖r • M‖ ≤ ‖(Interval.smul r A).absMax‖ :=
    Interval.norm_le_absMax (Interval.smul_outer r A hM)
  have hεM : ‖r • M‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (by gcongr) hε
  -- the point statement, at the member, is what everything below only widens
  have hpoint := MatExp.expIntegralDiff_mem_constCorrectionMatrix M hr η hεM ht0 htr
  have htail : r * MatExp.expRemainderBound (r • M) η
      ≤ r * MatExp.expRemainderBound (Interval.smul r A).absMax η :=
    mul_le_mul_of_nonneg_left (MatExp.expRemainderBound_mono η hnorm hε) hr.le
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have hpk := Interval.mem_mat_iff.mp hpoint j k
  -- each kept order of the member sits inside the order the box spans
  have hterm : ∀ i ∈ Finset.range η,
      (MatExp.intervalConstCorrTerm A r i).inf j k ≤ MatExp.constCorrTerm M r i j k
        ∧ MatExp.constCorrTerm M r i j k
            ≤ (MatExp.intervalConstCorrTerm A r i).sup j k := by
    intro i _
    have hs := Interval.smul_outer
      (MatExp.corrCoeff (i + 2) * r ^ (i + 2) * ((Nat.factorial (i + 2) : ℝ))⁻¹)
      (A.matPow (i + 1)) (Interval.matPow_outer A hM (i + 1))
    have h := Interval.mem_mat_iff.mp hs j k
    have hval : ((MatExp.corrCoeff (i + 2) * r ^ (i + 2)
        * ((Nat.factorial (i + 2) : ℝ))⁻¹) • M ^ (i + 1)) j k
          = MatExp.constCorrTerm M r i j k := by
      simp only [Matrix.smul_apply, smul_eq_mul, MatExp.constCorrTerm]
      ring
    rw [hval] at h
    exact h
  -- `min` and `max` are monotone, so the comparison survives the sum
  have hlow : ∑ i ∈ Finset.range η,
        min ((MatExp.intervalConstCorrTerm A r i).inf j k) 0
      ≤ ∑ i ∈ Finset.range η, min (MatExp.constCorrTerm M r i j k) 0 :=
    Finset.sum_le_sum fun i hi => min_le_min (hterm i hi).1 (le_refl 0)
  have hupp : ∑ i ∈ Finset.range η, max (MatExp.constCorrTerm M r i j k) 0
      ≤ ∑ i ∈ Finset.range η,
          max ((MatExp.intervalConstCorrTerm A r i).sup j k) 0 :=
    Finset.sum_le_sum fun i hi => max_le_max (hterm i hi).2 (le_refl 0)
  simp only [MatExp.constCorrectionMatrix] at hpk
  simp only [MatExp.intervalConstCorrectionMatrix]
  exact ⟨by linarith [hpk.1], by linarith [hpk.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
