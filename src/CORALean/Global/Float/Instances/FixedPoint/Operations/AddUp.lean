import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundUp

/-!
# Addition, rounded up

`exactAdd`, then `roundUp` back to `f` digits.
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

def addUp (a b : FixedPoint f) : FixedPoint f := roundUp (exactAdd a b)

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
