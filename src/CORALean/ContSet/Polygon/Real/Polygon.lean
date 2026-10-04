import CORALean.ContSet.SetUnion.API
import CORALean.ContSet.VPolytope.Real.API

/-!
# Polygons: finite unions of convex 2-D polytopes

CORA's `polygon` (`contSet/@polygon`) is a possibly non-convex region of the plane, held
through MATLAB's `polyshape`: a list of boundary vertices, with holes and several regions. A
`Polygon` here is `SetUnion (VPolytope (Vec ℝ 2))`: a finite list of convex polygons, each given
by its vertices, denoting their union. A region with holes is such a union too.

What is **not** formalized is the conversion from CORA's `polyshape` (boundary vertex lists with
holes) into convex pieces: that is a triangulation, which a polyshape computes with a
computational-geometry routine. A polygon is built here from convex pieces (`Polygon.ofPieces`),
never from a boundary. Consequently the methods that read the boundary (`getHoles`,
`getRegions`, `simplify`, `triangulation`, `splitIntoConvexSets`, `expandBoundaries`,
`removeCollinearPoints`, `isConvex`, `area`, ...) and those that are polygon boolean operations
(`and_`, `mldivide`, `subtract`) have no counterpart; `minus` by a vector is `Polygon.minus`.

The semantics is the union, so `SetUnion`'s `Plus` and `Reduce` instances are `Polygon`'s.
`Float/` is the same alias at the float polytope.

-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A polygon: a finite list of convex polygons, denoting their union. -/
abbrev Polygon : Type := SetUnion (VPolytope (Vec ℝ 2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
