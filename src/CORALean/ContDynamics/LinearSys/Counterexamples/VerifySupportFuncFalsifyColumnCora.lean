module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `LinearSys.verifySupportFuncFalsifyTestCora`: the time-point falsification test

In `@linearSys/private/priv_verifyRA_supportFunc.m`, `dist.affine_tp` is the
`(nrSteps+1) × nrSpecs` matrix of the time-point distances of the affine solution, one column per
halfspace (l. 334). After step `k` the test is `any(dist.affine_tp(k+1) > 0)` (l. 342): a linear
index into a column-major matrix, so for `k + 1 ≤ nrSteps + 1` it reads `(k+1, 1)`, the first
halfspace only. A positive distance of any other halfspace, which proves a violation at `t_k` when
there is no uncertain input, is not seen there; the time step is shrunk instead. Modelled with
MATLAB's column-major linear index, 1-based. Read from the source, not run.

# CORA misses a violation of the second halfspace

One step and two halfspaces, the row `dist.affine_tp(2,:) = [-1, 1]`: CORA's test is false
although the distance of the second halfspace is `1 > 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's test is false while a halfspace's time-point distance is positive
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- l. 342: `any(dist.affine_tp(k+1) > 0)` for `nrSteps + 1` rows, by the column-major linear index
`(k mod (nrSteps+1)) + 1, k / (nrSteps+1) + 1` of `k + 1`. -/
def LinearSys.verifySupportFuncFalsifyTestCora (nrSteps : ℕ) (tp : ℕ → ℕ → ℝ) (k : ℕ) : Prop :=
  0 < tp (k % (nrSteps + 1) + 1) (k / (nrSteps + 1) + 1)


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `affine_tp(2,:) = [-1, 1]` the test is false, yet the second distance is `1 > 0`. -/
theorem LinearSys.verifySupportFuncFalsifyTestCora_counterexample :
    let tp : ℕ → ℕ → ℝ := fun _ s => if s = 1 then -1 else 1
    ¬ LinearSys.verifySupportFuncFalsifyTestCora 1 tp 1 ∧ 0 < tp 2 2 := by
  intro tp
  refine ⟨?_, ?_⟩
  · simp [LinearSys.verifySupportFuncFalsifyTestCora, tp]
  · simp [tp]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
