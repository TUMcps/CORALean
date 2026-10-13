import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactMul
import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundDown

/-!
# Multiplication, rounded down

`exactMul`, then `roundDown` back to `f` digits.
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

def mulDown (a b : FixedPoint f) : FixedPoint f := roundDown (exactMul a b)

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
