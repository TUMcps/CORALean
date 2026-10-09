import CORALean.ContSet.Polygon.Real.Operations.Center
import CORALean.ContSet.Polygon.Real.Theorems.RegionCenterMem
import CORALean.ContSet.Polygon.Real.Theorems.IsCompact
import CORALean.ContSet.Polygon.Real.Theorems.VerticesHull
import CORALean.ContSet.Polygon.Real.Operations.Volume

/-!
# `Polygon.center` lies in the hull of the vertices

The centroid of a polygon of positive area lies in the convex hull of its vertices
(`Polygon.regionCenter_mem` at that hull, closed since the vertex set is finite). The centroid
itself is not computed; for a non-convex region (an L-shape, a ring) it may lie outside the region.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.center_mem_convexHull (P : Polygon) (h0 : Polygon.volume P ≠ 0) :
    Polygon.center P ∈ convexHull ℝ {v | v ∈ P.vertices} := by -- --- PROOF ---
  have hfin : {v | v ∈ P.vertices}.Finite := P.vertices.finite_toSet
  refine Polygon.regionCenter_mem (Polygon.isCompact_construct P) (convex_convexHull ℝ _)
    (hfin.isCompact_convexHull ℝ).isClosed ?_ h0
  rw [Polygon.convexHull_vertices]
  exact subset_convexHull ℝ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
