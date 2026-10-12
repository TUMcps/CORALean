import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexNotConvex
import Mathlib.Analysis.Convex.Hull

/-!
# `isPolytopeCex` is not a polytope

A convex hull of finitely many points is convex, and `isPolytopeCex.construct` is not.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- So it is not a polytope: a convex hull of finitely many points is convex. -/
theorem PolyZonotope.isPolytopeCex_not_polytope (s : Finset (Vec ℝ 2)) :
    PolyZonotope.isPolytopeCex.construct ≠ convexHull ℝ (s : Set (Vec ℝ 2)) := fun h =>
  PolyZonotope.isPolytopeCex_not_convex (h ▸ convex_convexHull ℝ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
