import CORALean.Global.Float.Instances.FixedPoint.Operations.Le

/-!
# The lesser of two fixed-point values

`le` decides it exactly, so this picks one of its two arguments and rounds
nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def minimum (a b : FixedPoint f) : FixedPoint f := if le a b then a else b

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
