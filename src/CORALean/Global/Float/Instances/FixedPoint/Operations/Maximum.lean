import CORALean.Global.Float.Instances.FixedPoint.Operations.Le

/-!
# The greater of two fixed-point values

`le` decides it exactly, so this picks one of its two arguments and rounds
nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def maximum (a b : FixedPoint f) : FixedPoint f := if le a b then b else a

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
