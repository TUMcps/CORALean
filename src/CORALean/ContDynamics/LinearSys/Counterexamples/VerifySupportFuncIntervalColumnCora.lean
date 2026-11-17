module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `LinearSys.verifySupportFuncIntervalTestCora`: the interval test with an uncertain input

In `@linearSys/private/priv_verifyRA_supportFunc.m`, `dist.affine_ti{s}` is the `nrSteps × 2`
matrix of the step's start and end distances, each plus the curvature term (l. 421). Without
an uncertain input the test is `all(dist.affine_ti{s}(k,:) < 0)`, both columns (l. 450). With one
(`isU`, l. 606) it is `all(dist.affine_ti{s}(k) + dist.overPU(k+1,s) < 0)`: a linear index into a
column-major matrix, so for `k ≤ nrSteps` it reads `(k, 1)`, the start of the step only. The
interval `[t_k, t_{k+1}]` is then removed from the unverified times although the bound at its end
is not checked. Modelled with MATLAB's column-major linear index, 1-based. Read from the source,
not run.

# CORA verifies a step whose outer bound at the end is positive

One step, `dist.affine_ti{s} = [-1, 1]`, `dist.overPU(2,s) = 0`: CORA's test holds and the step
is verified, while the outer distance `max(-1, 1) + 0 = 1 > 0` of the time-interval set does not
exclude a crossing of the halfspace.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's test passes while the larger end of the step's outer distance is positive
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- MATLAB's `X(k)` for an `r × 2` matrix `X` (1-based, column-major): row `(k-1) % r`, column
`(k-1) / r`. -/
def LinearSys.verifySupportFuncLinIndexCora (r : ℕ) (X : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  X ((k - 1) % r + 1) ((k - 1) / r + 1)

-- The model: CORA's code as printed, kept only to be refuted.
/-- l. 606: `all(dist.affine_ti{s}(k) + dist.overPU(k+1,s) < 0)` for `nrSteps` rows. -/
def LinearSys.verifySupportFuncIntervalTestCora (nrSteps : ℕ) (ti : ℕ → ℕ → ℝ) (overPU : ℕ → ℝ)
    (k : ℕ) : Prop :=
  LinearSys.verifySupportFuncLinIndexCora nrSteps ti k + overPU (k + 1) < 0


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `affine_ti = [-1, 1]` and `overPU = 0` the step passes, yet its larger end is `1 > 0`. -/
theorem LinearSys.verifySupportFuncIntervalTestCora_counterexample :
    let ti : ℕ → ℕ → ℝ := fun _ j => if j = 1 then -1 else 1
    LinearSys.verifySupportFuncIntervalTestCora 1 ti (fun _ => 0) 1 ∧
      0 < max (ti 1 1) (ti 1 2) + 0 := by
  intro ti
  refine ⟨?_, ?_⟩
  · simp [LinearSys.verifySupportFuncIntervalTestCora, LinearSys.verifySupportFuncLinIndexCora, ti]
  · simp [ti]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
