import CORALean.Global.Float.Instances.FixedPoint.Operations.Maximum
import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeIff

/-!
# `maximum` is exact

`le_iff` picks the larger side directly, which is what lets `maximum` absorb
a sign without widening anything. What `SoundFloatArithmetic.toReal_maximum`
needs from `FixedPoint`.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_maximum (a b : FixedPoint f) :
    toReal (maximum a b) = max (toReal a) (toReal b) := by
  by_cases h : le a b = true
  · rw [maximum, if_pos h, max_eq_right ((le_iff a b).mp h)]
  · rw [maximum, if_neg h, max_eq_left (not_le.mp (h ∘ (le_iff a b).mpr)).le]

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
