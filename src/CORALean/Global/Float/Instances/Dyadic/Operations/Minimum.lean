import CORALean.Global.Float.Instances.Dyadic.Operations.Le

/-!
# The lesser of two dyadics

`le` decides it exactly, so this picks one of its two arguments and rounds
nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def minimum (a b : Dyadic p) : Dyadic p := if le a b then a else b

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
