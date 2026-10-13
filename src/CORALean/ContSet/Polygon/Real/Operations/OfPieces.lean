import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.ofPieces`

The constructor: a polygon from convex pieces, which `polygon(V)` of CORA's constructor does
from a boundary, after a triangulation this file does not do.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the convex pieces `pieces`. -/
def Polygon.ofPieces (pieces : List (VPolytope (Vec ℝ 2))) : Polygon := ⟨pieces⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
