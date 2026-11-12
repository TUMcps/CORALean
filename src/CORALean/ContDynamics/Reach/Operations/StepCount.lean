module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# `Reach.stepCount`

The number of whole steps of MATLAB's `tStart:timeStep:tFinal` that CORA's `priv_reach_standard`
takes: `floor((tFinal - tStart) / timeStep)`, with the slack `10⁻⁹` that makes `0.3 / 0.1` three.
A stay that starts between two grid times of a hybrid automaton is cut short by the remainder,
less than one step.

## Inputs
* `tStart` – start time
* `tFinal` – final time
* `timeStep` – step size

## Output
* number of whole steps
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⌊(tFinal - tStart) / timeStep + 10⁻⁹⌋`, `0` for a step that is not positive. -/
def Reach.stepCount (tStart tFinal timeStep : ℚ) : ℕ :=
  if 0 < timeStep then ⌊(tFinal - tStart) / timeStep + 1 / 1000000000⌋₊ else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
