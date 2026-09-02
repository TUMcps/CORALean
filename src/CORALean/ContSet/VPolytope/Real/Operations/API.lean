import CORALean.ContSet.VPolytope.Real.Operations.Interval
import CORALean.ContSet.VPolytope.Real.Operations.LinComb
import CORALean.ContSet.VPolytope.Real.Operations.Map
import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
import CORALean.ContSet.VPolytope.Real.Operations.Plus

/-!
# What `VPolytope` computes

The operations vertices are good at: Minkowski sum, linear image, convex hull.
All exact, and all of them `Set.range V` under Mathlib's hull algebra once
`construct_eq_convexHull` is in hand. `interval` is the one that loses
something — a box around the vertices is a box around the hull, and wider.

Intersection is the operation missing, and it is the one a halfspace description
computes for free; `HPolytope` is for that.
-/
