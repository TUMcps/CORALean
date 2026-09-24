import CORALean.Global.Float.Instances.Dyadic.Operations.QuotUp
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundUp

/-!
# Division, rounded up

Rounded twice: `quotUp` already rounds while dividing, since a quotient of
dyadics is not dyadic, and the shift alone would keep `p` bits only for a
`p`-bit dividend, so `roundUp` rounds again.
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

-- rounded again: the shift alone would keep `p` bits only for a `p`-bit dividend
def divUp (a b : Dyadic p) : Dyadic p := roundUp (quotUp a b)

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
