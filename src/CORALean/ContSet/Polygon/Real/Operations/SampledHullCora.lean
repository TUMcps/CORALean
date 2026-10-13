import CORALean.ContSet.Polygon.Real.Polygon
import Mathlib.Analysis.Convex.Hull

/-!
# The polygon CORA builds from boundary samples, and its two tests against a set

`@ellipsoid/polygon.m` (documented "inner-approximative") takes `N = 1000` boundary points
`V = priv_boundary(E,N)` and returns `polygon(V)`; `@polygon/contains_.m` l. 69 and
`@polygon/isIntersecting_.m` l. 49 apply that conversion to an ellipsoid operand `S`.

Abstracted, not modelled: `polygon(V)` is `polyshape(V)`; for boundary points of a convex body in
angular order it is their convex hull, taken here for every finite point set. `N` and the point
positions are not modelled: the results hold for every finite sample. The two tests are on
regions: `contains_` l. 71-78 accepts when `withinTol(area(P), area(union(P, S')), tol)` (taken as
an absolute tolerance), `isIntersecting_` l. 52 returns `overlaps(P, S')`, here that the regions
share a point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The region of `polygon(V)` for the sampled boundary points `V`. -/
def Polygon.sampledHullCora (V : Set (Vec ℝ 2)) : Set (Vec ℝ 2) := convexHull ℝ V

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
