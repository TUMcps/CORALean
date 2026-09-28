import CORALean.Global.Float.Instances.Flint.Operations.Le

/-!
# The greater of two values

`le` decides it exactly, so this picks one of its two arguments and rounds
nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def maximum (a b : Flint p) : Flint p := if le a b then b else a

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
