module

public import CORALean.ContSet.Interval.Real.Theorems.IntervalMatrixEq

@[expose] public section

/-!
# The corner `sup` is `radius` from the centre

The upper corner minus the centre is the half-width, so the corner is at distance `‖radius‖₂`
from the centre.
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
