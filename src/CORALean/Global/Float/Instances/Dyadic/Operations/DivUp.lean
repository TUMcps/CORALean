import CORALean.Global.Float.Instances.Dyadic.Operations.QuotUp
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundUp

/-!
# Division, rounded up

Rounded twice: `quotUp` already rounds while dividing, since a quotient of
dyadics is not dyadic, and its shift leaves it at least `p` bits and up to the
dividend's length more, so `roundUp` returns it to `p`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   25-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

-- rounded again: the quotient carries `p` bits and up to the dividend's length more
def divUp (a b : Dyadic p) : Dyadic p := roundUp (quotUp a b)

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
