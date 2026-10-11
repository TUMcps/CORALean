import CORALean.Global.Float.Instances.Dyadic.Operations.AlignExp
import CORALean.Global.Float.Instances.Dyadic.Operations.CoarsenDown
import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundDown

/-!
# Addition, rounded down

`exactAdd` of both operands coarsened downward (`coarsenDown`: a no-op unless one sits more than
`alignGuard p` binades below the other, which keeps `2 ^ gap` small), then `roundDown` back to
`p` bits.
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

def addDown (a b : Dyadic p) : Dyadic p :=
  roundDown (exactAdd (coarsenDown (alignExp a b) a) (coarsenDown (alignExp a b) b))

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
