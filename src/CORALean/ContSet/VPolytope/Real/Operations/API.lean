import CORALean.ContSet.VPolytope.Real.Operations.Map
import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
import CORALean.ContSet.VPolytope.Real.Operations.Plus
import CORALean.ContSet.VPolytope.Real.Operations.LinComb

/-!
# What `VPolytope` computes

The operations vertices are good at: Minkowski sum, linear image, convex hull.
All exact, and all of them `Set.range V` under Mathlib's hull algebra once
`construct_eq_convexHull` is in hand.
-/
