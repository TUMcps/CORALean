import CORALean.ContSet.Polygon.Real.Operations.ConvHull

/-!
# `Polygon.isConvex`

CORA's `polygon/isConvex` compares the boundary-vertex counts of the polygon and of its convex
hull. At the region, convex means equal to the convex hull: the hull of the vertices of all
pieces lies inside the region (`Polygon.isConvex_iff`). The vertex count is not formalized (R-PG).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The convex hull of the pieces lies inside the region. -/
def Polygon.isConvex (P : Polygon) : Prop :=
  VPolytope.construct (Polygon.convHull P) ⊆ ContSet.construct P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
