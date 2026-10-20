module

public import CORALean.ContSet.Polygon.Real.Polygon

@[expose] public section

/-!
# `Polygon.vertices`

CORA's `polygon/vertices_`: the vertices of the pieces. For a polyshape CORA returns the
boundary vertices; the vertices of the convex pieces are not those (a piece's vertex may lie in
the interior of the union), but they hold the same hull, see `Polygon.convexHull_vertices`.

## Inputs
* `P` – polygon

## Output
* the vertices of every piece
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertices of every piece. -/
def Polygon.vertices (P : Polygon) : List (Vec ℝ 2) :=
  P.sets.flatMap fun p => List.ofFn p.V

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
