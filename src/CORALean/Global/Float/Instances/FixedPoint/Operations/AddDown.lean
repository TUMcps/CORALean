import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundDown

/-!
# Addition, rounded down

`exactAdd`, then `roundDown` back to `f` digits.
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

def addDown (a b : FixedPoint f) : FixedPoint f := roundDown (exactAdd a b)

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
