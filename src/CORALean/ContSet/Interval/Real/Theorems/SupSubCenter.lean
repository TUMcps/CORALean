module

public import CORALean.ContSet.Interval.Real.Theorems.IntervalMatrixEq

@[expose] public section

/-!
# The corner `sup` is `radius` from the center

The upper corner minus the center is the half-width, so the corner is at distance `‖radius‖₂`
from the center.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the upper bound minus the center is the radius
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sup_sub_center (I : Interval (Vec ℝ n)) : I.sup - I.center = I.radius := by
  have h := Interval.center_add_radius I
  rw [← h]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
