import CORALean.ContSet.Polygon.Real.Operations.ConvHull
import CORALean.ContSet.Polygon.Real.Theorems.VerticesHull

/-!
# `Polygon.convHull` is the convex hull

Exactly.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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
