import CORALean.ContSet.VPolytope.Real.Operations.Interval
import CORALean.ContSet.VPolytope.Real.Operations.LinComb
import CORALean.ContSet.VPolytope.Real.Operations.Map
import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
import CORALean.ContSet.VPolytope.Real.Operations.Plus
import CORALean.ContSet.VPolytope.Real.Operations.SupportBound

/-!
# What `VPolytope` computes

The operations vertices are good at: Minkowski sum, linear image, convex hull.
All exact, and all of them `Set.range V` under Mathlib's hull algebra once
`construct_eq_convexHull` is in hand.

`supportBound` is what the other representation needs a linear program for, and
here it is a maximum over the vertex list — attained rather than approached, and
requiring no certificate. `interval` is that at the `2n` coordinate directions,
and the one operation that loses something: a box around the vertices is a box
around the hull, and wider.

Intersection is the operation missing, and it is the one a halfspace description
computes for free; `HPolytope` is for that.
-/
