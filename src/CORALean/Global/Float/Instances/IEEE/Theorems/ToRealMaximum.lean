module

public import CORALean.Global.Float.Instances.IEEE.Operations.Basic
public import CORALean.Global.Float.Instances.IEEE.Theorems.Basic

@[expose] public section

/-!
# The greater of two numbers is exact

`le` decides the order exactly, so the argument picked is the maximum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_maximum (a b : IEEE fmt) :
    (maximum a b).toReal = max a.toReal b.toReal := by
  by_cases h : le a b = true
  · rw [maximum, if_pos h, max_eq_right ((le_iff a b).mp h)]
  · rw [maximum, if_neg h, max_eq_left (not_le.mp (h ∘ (le_iff a b).mpr)).le]

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
