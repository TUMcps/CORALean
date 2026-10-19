module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# The box's input remainder contains every member's

`E(r)·r` is a box of one uniform width, so widening it to a whole interval
matrix is widening that one number: `expRemainderBound_mono` at
`norm_le_absMax`, and nothing else. Stated as a containment between the two
interval matrices, which is how an input solution uses it — the point
remainder is where a member's tail is shown to lie, and this carries that into
the set-valued one.

`hε` is stated at the dominating matrix of `r • A`, checkable before a member is
fixed, as everywhere else in this directory.
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

/-- Every matrix the point remainder at a member admits is admitted by the
remainder of the whole box. -/
theorem MatExp.intervalInputRemainder_contains (A : Interval (Mat ℝ n n)) {r : ℝ}
    (hr : 0 < r) (η : ℕ) (hε : ‖(Interval.smul r A).absMax‖ / ((η : ℝ) + 2) < 1)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) : -- --- CONCL ---
    (MatExp.inputRemainder M r η).construct
      ⊆ (MatExp.intervalInputRemainder A r η).construct := by -- --- PROOF ---
  intro N hN
  have hnorm : ‖r • M‖ ≤ ‖(Interval.smul r A).absMax‖ :=
    Interval.norm_le_absMax (Interval.smul_outer r A hM)
  -- one number widens, and the step scales it the same way on both sides
  have htail := mul_le_mul_of_nonneg_left
    (MatExp.expRemainderBound_mono η hnorm hε) hr.le
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have h := Interval.mem_mat_iff.mp hN j k
  simp only [MatExp.inputRemainder] at h
  simp only [MatExp.intervalInputRemainder]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
