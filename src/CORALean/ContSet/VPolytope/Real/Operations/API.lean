import CORALean.ContSet.VPolytope.Real.Operations.And
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

`ofInterval` is a box as its `2ⁿ` corners, which is what `and` goes through:
intersection is the operation vertices are worst at, its result's vertices being
generally none of either operand's, so each hull is boxed, the boxes intersected
exactly, and the corners taken. Sound and loose, and exact when both operands
were boxes. The tight version is the conversion `Polytope` does not have.
-/
