import CORALean.ContSet.Zonotope.Float.Operations.MatMul
import CORALean.ContSet.Zonotope.Float.Operations.OfIntervalMat

/-!
# `GZonotope.matMulIntervalMat`

A matrix zonotope times an interval matrix, CORA's `mtimes(matZonotope, intervalMatrix)`:
the interval matrix converted by `ofIntervalMat`, one generator per entry, and then
`matMul`, so each entry of the interval factor stays a dependency of the product rather
than a box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {p q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GZonotope.matMulIntervalMat (M : GZonotope (Mat 𝕋 p q)) (I : Interval (Mat 𝕋 q r)) :
    GZonotope (Mat 𝕋 p r) :=
  GZonotope.matMul M (GZonotope.ofIntervalMat I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
