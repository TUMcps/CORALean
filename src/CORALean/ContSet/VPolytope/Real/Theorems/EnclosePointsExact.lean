import CORALean.ContSet.VPolytope.Real.Operations.EnclosePoints
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

/-!
# `VPolytope.enclosePoints` is exactly the convex hull of the points

An equality, not an enclosure: the polytope is the smallest convex set containing the points.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.enclosePoints_exact {N : ℕ} (pts : Fin N → Vec ℝ n) :
    (VPolytope.enclosePoints pts).construct = convexHull ℝ (Set.range pts) :=
  VPolytope.construct_eq_convexHull _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
