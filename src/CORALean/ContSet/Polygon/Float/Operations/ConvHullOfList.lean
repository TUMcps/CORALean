import CORALean.ContSet.Polygon.Float.Polygon
import CORALean.ContSet.VPolytope.Float.Operations.ConvHull
import CORALean.ContSet.VPolytope.Float.Operations.EmptySet

/-!
# The hull of a list of pieces

The pieces' hulls folded with `VPolytope.convHull`, from the right. The empty list is the empty
polytope and a single piece is itself, so no box is joined with a box that holds nothing.
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

def Polygon.convHullOfList : List (VPolytope 𝕋 2) → VPolytope 𝕋 2
  | [] => VPolytope.emptySet 𝕋 2
  | [p] => p
  | p :: q :: ps => p.convHull (Polygon.convHullOfList (q :: ps))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
