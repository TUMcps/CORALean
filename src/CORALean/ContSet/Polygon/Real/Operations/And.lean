import CORALean.ContSet.Polygon.Real.Polygon
import CORALean.ContSet.VPolytope.Real.Operations.Intersection

/-!
# `Polygon.and`

CORA's `polygon/and_` (`intersect` of two polyshapes) at two polygons given as convex pieces:
the intersection of two unions is the union of the pairwise piece intersections, each computed by
`VPolytope.intersection` at the given directions. It is an outer bound of the intersection
(`Polygon.and_outer`); it is exact where each pairwise `VPolytope.intersection` is (the
directions contain the facet normals), which is not proved. The region identity itself, without
the conversion of a piece intersection back to vertices, is `Polygon.and_region`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- All pairs of pieces, intersected at the directions `Aq`. -/
noncomputable def Polygon.and {q : ℕ} (P Q : Polygon) (Aq : Fin q → (Vec ℝ 2 →ₗ[ℝ] ℝ)) :
    Polygon :=
  ⟨(P.sets.product Q.sets).map fun pq => VPolytope.intersection pq.1 pq.2 Aq Aq⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
