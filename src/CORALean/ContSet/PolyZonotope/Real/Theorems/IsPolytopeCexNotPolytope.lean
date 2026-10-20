module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexNotConvex
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `isPolytopeCex` is not a polytope

A convex hull of finitely many points is convex, and `isPolytopeCex.construct` is not.

## Inputs
* `s` – finite set of points

## Hypotheses
* none

## Conclusion
* the counterexample set is not the hull of the points
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- So it is not a polytope: a convex hull of finitely many points is convex. -/
theorem PolyZonotope.isPolytopeCex_not_polytope (s : Finset (Vec ℝ 2)) :
    PolyZonotope.isPolytopeCex.construct ≠ convexHull ℝ (s : Set (Vec ℝ 2)) := fun h =>
  PolyZonotope.isPolytopeCex_not_convex (h ▸ convex_convexHull ℝ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
