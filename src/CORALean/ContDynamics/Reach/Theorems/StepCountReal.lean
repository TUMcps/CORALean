module

public import CORALean.ContDynamics.Reach.Theorems.StepCountLower
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# The steps `Reach.stepCount` takes, read in the reals

`Reach.le_stepCount_mul` for a real time: a time `τ ≥ 0` that ends a step before the horizon is
within the `stepCount` steps, and there is at least one.

## Inputs
* `tStart` – start time
* `tFinal` – final time
* `timeStep` – step size
* `τ` – time

## Hypotheses
* `hΔ` – the step is positive
* `h0` – the time is nonnegative
* `hτ` – the time ends one step before the horizon

## Conclusion
* the steps are not zero, and span the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem Reach.stepCount_real {tStart tFinal timeStep : ℚ} (hΔ : 0 < timeStep) {τ : ℝ}
    (h0 : 0 ≤ τ) (hτ : τ + timeStep ≤ tFinal - tStart) : -- --- CONCL ---
    0 < Reach.stepCount tStart tFinal timeStep ∧
      τ ≤ (Reach.stepCount tStart tFinal timeStep : ℝ) * timeStep := by -- --- PROOF ---
  have hR : τ ≤ ((tFinal - tStart - timeStep : ℚ) : ℝ) := by
    push_cast; linarith
  have h := Reach.le_stepCount_mul (tStart := tStart) (tFinal := tFinal) hΔ
    (τ := tFinal - tStart - timeStep) (by linarith)
  refine ⟨h.2 (by
    have : (0 : ℝ) ≤ ((tFinal - tStart - timeStep : ℚ) : ℝ) := h0.trans hR
    exact_mod_cast this), ?_⟩
  have h1 : ((tFinal - tStart - timeStep : ℚ) : ℝ) ≤ ((Reach.stepCount tStart tFinal timeStep *
      timeStep : ℚ) : ℝ) := by exact_mod_cast h.1
  push_cast at h1
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
