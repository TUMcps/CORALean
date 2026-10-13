import CORALean.ContSet.Polygon.Real.Operations.ConvHull
import CORALean.ContSet.Polygon.Real.Theorems.VerticesHull

/-!
# `Polygon.convHull` is the convex hull

Exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.convHull_exact (P : Polygon) :
    VPolytope.construct (Polygon.convHull P) =
      convexHull ℝ (ContSet.construct P) := by
  rw [VPolytope.construct_eq_convexHull, ← Polygon.convexHull_vertices]
  congr 1
  ext v
  simp [Polygon.convHull, List.mem_iff_get]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
