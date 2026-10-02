import CORALean.ContSet.Polygon.Float.Operations.ConvHullOfList

/-!
# `Polygon.convHull` over floats

CORA's `convHull_` of a polygon, and `polytope(pgon)`, the polytope on the vertices of its hull:
the V-polytope joining every piece's vertex list, with the pieces' error boxes hulled.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.convHull (P : Polygon 𝕋) : VPolytope 𝕋 2 :=
  Polygon.convHullOfList P.sets

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
