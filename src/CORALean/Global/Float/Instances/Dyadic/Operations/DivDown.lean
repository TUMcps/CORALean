import CORALean.Global.Float.Instances.Dyadic.Operations.QuotDown
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundDown

/-!
# Division, rounded down

Rounded twice, `quotDown`'s mirror: `roundDown` rounds again past the
rounding `quotDown` already did while dividing.
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

def divDown (a b : Dyadic p) : Dyadic p := roundDown (quotDown a b)

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
