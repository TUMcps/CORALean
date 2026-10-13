import CORALean.Global.Float.Instances.Dyadic.Operations.ExactMul
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundUp

/-!
# Multiplication, rounded up

`exactMul`, then `roundUp` back to `p` bits.
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

def mulUp (a b : Dyadic p) : Dyadic p := roundUp (exactMul a b)

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
