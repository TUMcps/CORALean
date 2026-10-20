module

public import CORALean.ContSet.SetUnion.SetUnion
public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# Polygons: finite unions of convex 2-D polytopes

CORA's `polygon` (`contSet/@polygon`) is a possibly non-convex region of the plane held through
MATLAB's `polyshape`: boundary vertices, with holes and several regions. A `Polygon` here is
`SetUnion (VPolytope (Vec ℝ 2))`, a finite list of convex polygons denoting their union. **Not**
formalized is the conversion from `polyshape` into convex pieces, a triangulation: a polygon is
built from convex pieces (`Polygon.ofPieces`), never from a boundary. Methods reading the boundary
(`removeCollinearPoints`, `compact_`, ...) have no counterpart (R-PG in
`references/coverage/README.md`); those a region-level statement captures are stated against the
region the pieces denote (`triangulation`, `subtract`).

## Inputs
* none

## Output
* A polygon: a finite list of convex polygons, denoting their union
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A polygon: a finite list of convex polygons, denoting their union. -/
abbrev Polygon : Type := SetUnion (VPolytope (Vec ℝ 2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
