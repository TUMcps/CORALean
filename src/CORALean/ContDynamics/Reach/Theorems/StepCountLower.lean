module

public import CORALean.ContDynamics.Reach.Operations.StepCount

@[expose] public section

/-!
# The steps `Reach.stepCount` takes reach to within one step of the horizon

`N` steps of `timeStep` fall short of the horizon by less than one step. A time that ends one
step before the horizon is therefore within `N` steps, and `N` is at least one.

## Inputs
* `tStart` – start time
* `tFinal` – final time
* `timeStep` – step size
* `τ` – time

## Hypotheses
* `hΔ` – the step is positive
* `hτ` – the time ends one step before the horizon

## Conclusion
* the time is within the steps, and the steps are not zero
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A time at least a step before the horizon is within the `stepCount` steps, and the count is
positive if the time is nonnegative. -/
theorem Reach.le_stepCount_mul {tStart tFinal timeStep : ℚ} (hΔ : 0 < timeStep) {τ : ℚ}
    (hτ : τ + timeStep ≤ tFinal - tStart) : -- --- CONCL ---
    τ ≤ Reach.stepCount tStart tFinal timeStep * timeStep ∧
      (0 ≤ τ → 0 < Reach.stepCount tStart tFinal timeStep) := by -- --- PROOF ---
  unfold Reach.stepCount
  rw [if_pos hΔ]
  have hq : τ / timeStep + 1 ≤ (tFinal - tStart) / timeStep := by
    have h1 : τ / timeStep + 1 = (τ + timeStep) / timeStep := by field_simp
    rw [h1]
    exact div_le_div_of_nonneg_right hτ hΔ.le
  have hfl : ((tFinal - tStart) / timeStep + 1 / 1000000000) - 1 <
      ⌊(tFinal - tStart) / timeStep + 1 / 1000000000⌋₊ := by
    have := Nat.lt_floor_add_one ((tFinal - tStart) / timeStep + 1 / 1000000000)
    linarith
  constructor
  · have : τ / timeStep < ⌊(tFinal - tStart) / timeStep + 1 / 1000000000⌋₊ := by linarith
    have := (div_lt_iff₀ hΔ).mp this
    exact this.le
  · intro h0
    have : (0 : ℚ) < ⌊(tFinal - tStart) / timeStep + 1 / 1000000000⌋₊ := by
      have : 0 ≤ τ / timeStep := div_nonneg h0 hΔ.le
      linarith
    exact_mod_cast this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
