import CORALean.Global.Float.Instances.Dyadic.Operations.ExactMul
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundDown

/-!
# Multiplication, rounded down

`exactMul`, then `roundDown` back to `p` bits.
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

def mulDown (a b : Dyadic p) : Dyadic p := roundDown (exactMul a b)

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
