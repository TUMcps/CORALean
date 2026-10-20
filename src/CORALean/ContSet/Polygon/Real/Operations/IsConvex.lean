module

public import CORALean.ContSet.Polygon.Real.Operations.ConvHull
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# `Polygon.isConvex`

CORA's `polygon/isConvex` compares the boundary-vertex counts of the polygon and of its convex
hull. At the region, convex means equal to the convex hull: the hull of the vertices of all
pieces lies inside the region (`Polygon.isConvex_iff`). The vertex count is not formalized (R-PG).

## Inputs
* `P` – polygon

## Output
* the convex hull of the pieces lies inside the region
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The convex hull of the pieces lies inside the region. -/
def Polygon.isConvex (P : Polygon) : Prop :=
  VPolytope.construct (Polygon.convHull P) ⊆ ContSet.construct P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
