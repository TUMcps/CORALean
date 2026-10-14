module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealDef
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A positive fixed-point value has a positive mantissa

The scale `10 ^ d` is positive, so the sign is the mantissa's. Both
`divDown_le_div` and `le_divUp` need the divisor's mantissa positive, to
divide by it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem mantissa_pos {b : FixedPoint f} (hb : 0 < toReal b) : 0 < b.m := by
  rw [toReal_def] at hb
  rcases div_pos_iff.mp hb with ⟨ha, _⟩ | ⟨_, hc⟩
  · exact_mod_cast ha
  · exact absurd hc (not_lt.mpr (by positivity))

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
