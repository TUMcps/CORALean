import CORALean.Global.Float.Instances.IEEE.Operations.Minimum
import CORALean.Global.Float.Instances.IEEE.Theorems.LeIff

/-!
# The lesser of two numbers is exact

`le` decides the order exactly, so the argument picked is the minimum.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_minimum (a b : IEEE fmt) :
    (minimum a b).toReal = min a.toReal b.toReal := by
  by_cases h : le a b = true
  · rw [minimum, if_pos h, min_eq_left ((le_iff a b).mp h)]
  · rw [minimum, if_neg h, min_eq_right (not_le.mp (h ∘ (le_iff a b).mpr)).le]

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
