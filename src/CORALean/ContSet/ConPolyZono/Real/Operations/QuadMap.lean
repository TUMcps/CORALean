import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMapDep

/-!
# `ConPolyZono.quadMap`

CORA's `@conPolyZono/quadMap`: `quadMapDep` run on `dependent`, exactly as
`PolyZonotope.quadMap` does and for the same reason — the expansion is stated
on a set whose coefficients are all dependent. Here `dependent` also widens
the constraints with zero rows for the fresh factors, which is what keeps the
two arrangements in step.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n k : ℕ}

def ConPolyZono.quadMap (Q : Fin k → Mat ℝ n n) (C : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ k) :=
  ConPolyZono.quadMapDep Q C.dependent

end CORALean.Real
