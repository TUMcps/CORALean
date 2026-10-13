import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
import CORALean.ContSet.VPolytope.Real.Operations.ConstructEmptySet
import CORALean.ContSet.VPolytope.Real.Operations.Point
import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint
import CORALean.ContSet.VPolytope.Real.Operations.IntersectionH
import CORALean.ContSet.VPolytope.Real.Operations.IntersectionHIsCompact
import CORALean.ContSet.VPolytope.Real.Operations.Intersection
import CORALean.ContSet.VPolytope.Real.Operations.LinComb
import CORALean.ContSet.VPolytope.Real.Operations.Map
import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
import CORALean.ContSet.VPolytope.Real.Operations.MtimesEqMap
import CORALean.ContSet.VPolytope.Real.Operations.Bilin
import CORALean.ContSet.VPolytope.Real.Operations.ColLin
import CORALean.ContSet.VPolytope.Real.Operations.MatPolytope
import CORALean.ContSet.VPolytope.Real.Operations.MtimesMatPolytope
import CORALean.ContSet.VPolytope.Real.Operations.Plus
import CORALean.ContSet.VPolytope.Real.Operations.LeOfForallLe
import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
import CORALean.ContSet.VPolytope.Real.Operations.Project
import CORALean.ContSet.VPolytope.Real.Operations.EnclosePoints
import CORALean.ContSet.VPolytope.Real.Operations.ConvHull
import CORALean.ContSet.VPolytope.Real.Operations.Or
import CORALean.ContSet.VPolytope.Real.Operations.ProjectHighDim
import CORALean.ContSet.VPolytope.Real.Operations.Center
import CORALean.ContSet.VPolytope.Real.Operations.CartProd
import CORALean.ContSet.VPolytope.Real.Operations.KNeZeroOfNonempty
import CORALean.ContSet.VPolytope.Real.Operations.HausdorffDist
import CORALean.ContSet.VPolytope.Real.Operations.DistPoint
import CORALean.ContSet.VPolytope.Real.Operations.RepresentsaHalfspaceCora

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

`intersection` is the operation vertices are worst at, its result's vertices
being generally none of either operand's, so it goes out to halfspaces on
directions the caller names, intersects there for free, and comes back by
vertex enumeration. Exact when the directions carry both operands' facets, enclosing
otherwise; the float layer, which cannot enumerate vertices, goes through boxes
instead.

`EmptySet` and `Point` are the two vertex lists short enough to name: none, and
one. `bilin` pairs every vertex of one operand against the other's;
`mtimesMatPolytope` is `bilin` at `*ᵥ`, a matrix polytope's vertices standing in
for its matrices.
-/
