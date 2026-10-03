import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.representsaEmptySet`, over a floating-point scalar

CORA's `polygon/representsa_` at `'emptySet'`: no piece has a vertex. Generic in the scalar, since
a count of vertices is a natural number.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.representsaEmptySet (P : Polygon 𝕋) : Bool :=
  P.sets.all fun p => p.k == 0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
