import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.PolyZonotope.Float.Operations.Midpoint

/-!
# What storing the midpoint leaves to pay

Split out of `LinComb.lean` (issue #62): read again by
`Theorems/LinCombOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Storing the lower of the two directed midpoints leaves this much to pay. -/
def PolyZonotope.midpointResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => half (addDown (a i) (b i)))
    (fun i => half (addUp (a i) (b i))) (PolyZonotope.midpoint a b)

end CORALean.Float
