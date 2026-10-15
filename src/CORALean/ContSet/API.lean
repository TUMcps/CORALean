module

public import CORALean.ContSet.ContSet.API
public import CORALean.ContSet.Equality.API
public import CORALean.ContSet.OptEmpty.API
public import CORALean.ContSet.SetUnion.API
public import CORALean.ContSet.SetIntersection.API
public import CORALean.ContSet.EmptySet.API
public import CORALean.ContSet.Fullspace.API
public import CORALean.ContSet.InflatedContSet.API
public import CORALean.ContSet.Interval.API
public import CORALean.ContSet.Zonotope.API
public import CORALean.ContSet.Polygon.API
public import CORALean.ContSet.ZonoBundle.API
public import CORALean.ContSet.SpectraShadow.API
public import CORALean.ContSet.Ellipsoid.API
public import CORALean.ContSet.Capsule.API
public import CORALean.ContSet.StarSet.API
public import CORALean.ContSet.SupportFunction.API
public import CORALean.ContSet.LevelSet.API
public import CORALean.ContSet.HPolytope.API
public import CORALean.ContSet.VPolytope.API
public import CORALean.ContSet.Conversion.API
public import CORALean.ContSet.ConZonotope.API
public import CORALean.ContSet.PolyZonotope.API
public import CORALean.ContSet.ConPolyZono.API
public import CORALean.ContSet.Taylm.API
public import CORALean.ContSet.Zoo.API
public import CORALean.ContSet.ProbZonotope.API

/-!
# Set representations, collected

`ContSet` is the interface every representation instantiates; `InflatedContSet`
is what a float representation adds on top of its exact counterpart, beside it.
`EmptySet` and `Fullspace` are `∅` and the whole space as representations, as
CORA has them; `OptEmpty` wraps one for a result that may be `∅`, and
`SetUnion`/`SetIntersection` a list's union or intersection, generic rather than layered.
`Ellipsoid` is the one representation whose support function is closed form in
every direction at once, making the conversions out of it tight without a linear program.

`HPolytope` and `VPolytope` describe the same sets, by halfspaces and by
vertices, and are separate representations because converting between them is
vertex enumeration. `ConZonotope` is a zonotope whose coefficients a halfspace
description cuts down; `PolyZonotope` is the first representation here that need
not be convex, and `ConPolyZono` constrains it the same way — except that its
constraints are polynomial in the factors and so cannot be a polytope. There a
constraint's right-hand side is an interval, so a rounded bound has a direction
to be widened in, which is what gives `intersection` a float counterpart.
Five intersect exactly, three interestingly: a box and a halfspace description by
construction, the constrained pair in its constraints, `ZonoBundle` side by side.

`Capsule` stands apart: convex and compact, but closed under none of `Plus`,
`Mtimes`, or `LinComb` — CORA uses it to describe an obstacle, not to carry a set.
-/
