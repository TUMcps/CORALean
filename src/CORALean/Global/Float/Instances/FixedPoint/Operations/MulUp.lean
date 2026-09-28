import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactMul
import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundUp

/-!
# Multiplication, rounded up

`exactMul`, then `roundUp` back to `f` digits.
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

def mulUp (a b : FixedPoint f) : FixedPoint f := roundUp (exactMul a b)

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
