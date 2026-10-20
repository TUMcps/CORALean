module

public import CORALean.ContSet.Polygon.Real.Polygon

@[expose] public section

/-!
# `Polygon.splitIntoConvexSets`

CORA's `polygon/splitIntoConvexSets` triangulates the polyshape and merges neighbouring triangles
while their union stays convex. A polygon here is already a list of convex pieces, so the pieces
are a convex split of the region (`Polygon.splitIntoConvexSets_exact`). The pieces CORA returns
(a triangulation, greedily merged) differ from the stored ones; the region they cover is the
same (R-PG).

## Inputs
* `P` – polygon

## Output
* the stored convex pieces
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stored convex pieces. -/
def Polygon.splitIntoConvexSets (P : Polygon) : List (VPolytope (Vec ℝ 2)) := P.sets

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
