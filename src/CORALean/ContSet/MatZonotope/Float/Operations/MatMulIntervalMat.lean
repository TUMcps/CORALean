import CORALean.ContSet.MatZonotope.Float.Operations.MatMul
import CORALean.ContSet.MatZonotope.Float.Operations.OfInterval

/-!
# `MatZonotope.matMulIntervalMat`

A matrix zonotope times an interval matrix, CORA's `mtimes(matZonotope, intervalMatrix)`:
the interval matrix converted by `ofInterval`, one generator per entry, and then
`matMul`, so each entry of the interval factor stays a dependency of the product rather
than a box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {p q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatZonotope.matMulIntervalMat (M : MatZonotope 𝕋 p q) (I : Interval (Mat 𝕋 q r)) :
    MatZonotope 𝕋 p r :=
  MatZonotope.matMul M (MatZonotope.ofInterval I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
