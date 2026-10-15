module

public import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructEmptySet
public import CORALean.ContSet.VPolytope.Real.Operations.Point
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint
public import CORALean.ContSet.VPolytope.Real.Operations.IntersectionH
public import CORALean.ContSet.VPolytope.Real.Operations.IntersectionHIsCompact
public import CORALean.ContSet.VPolytope.Real.Operations.Intersection
public import CORALean.ContSet.VPolytope.Real.Operations.LinComb
public import CORALean.ContSet.VPolytope.Real.Operations.Map
public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.ContSet.VPolytope.Real.Operations.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.Bilin
public import CORALean.ContSet.VPolytope.Real.Operations.ColLin
public import CORALean.ContSet.VPolytope.Real.Operations.MtimesMatPolytope
public import CORALean.ContSet.VPolytope.Real.Operations.Plus
public import CORALean.ContSet.VPolytope.Real.Operations.LeOfForallLe
public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Real.Operations.ConvHull
public import CORALean.ContSet.VPolytope.Real.Operations.Or
public import CORALean.ContSet.VPolytope.Real.Operations.ProjectHighDim
public import CORALean.ContSet.VPolytope.Real.Operations.Center
public import CORALean.ContSet.VPolytope.Real.Operations.CartProd
public import CORALean.ContSet.VPolytope.Real.Operations.KNeZeroOfNonempty
public import CORALean.ContSet.VPolytope.Real.Operations.HausdorffDist
public import CORALean.ContSet.VPolytope.Real.Operations.DistPoint
public import CORALean.ContSet.VPolytope.Real.Operations.Mpower

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
