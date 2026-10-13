import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeIff

/-!
# `le` only approves what is true

The direction `SoundFloatArithmetic` asks for; the converse holds too
(`le_iff`), but nothing here needs it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The direction `SoundFloatArithmetic` asks for; the converse holds too
(`le_iff`), but nothing here needs it. -/
theorem toReal_le_of_le {a b : FixedPoint f} (h : le a b = true) : toReal a ≤ toReal b :=
  (le_iff a b).mp h

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
