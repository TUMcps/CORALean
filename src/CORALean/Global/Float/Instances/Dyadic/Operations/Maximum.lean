import CORALean.Global.Float.Instances.Dyadic.Operations.Le

/-!
# The greater of two dyadics

`le` decides it exactly, so this picks one of its two arguments and rounds
nothing.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def maximum (a b : Dyadic p) : Dyadic p := if le a b then b else a

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
