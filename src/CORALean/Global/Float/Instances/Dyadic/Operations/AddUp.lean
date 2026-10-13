import CORALean.Global.Float.Instances.Dyadic.Operations.AlignExp
import CORALean.Global.Float.Instances.Dyadic.Operations.CoarsenUp
import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundUp

/-!
# Addition, rounded up

`exactAdd` of both operands coarsened upward (`coarsenUp`: a no-op unless one sits more than
`alignGuard p` binades below the other, which keeps `2 ^ gap` small), then `roundUp` back to
`p` bits.
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

def addUp (a b : Dyadic p) : Dyadic p :=
  roundUp (exactAdd (coarsenUp (alignExp a b) a) (coarsenUp (alignExp a b) b))

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
