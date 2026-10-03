import CORALean.ContSet.ContSet.API
import CORALean.ContSet.WithEmpty.API
import CORALean.ContSet.SetUnion.API
import CORALean.ContSet.SetIntersection.API
import CORALean.ContSet.EmptySet.API
import CORALean.ContSet.Fullspace.API
import CORALean.ContSet.InflatedContSet.API
import CORALean.ContSet.Interval.API
import CORALean.ContSet.Zonotope.API
import CORALean.ContSet.MatZonotope.API
import CORALean.ContSet.Polygon.API
import CORALean.ContSet.ZonoBundle.API
import CORALean.ContSet.SpectraShadow.API
import CORALean.ContSet.Ellipsoid.API
import CORALean.ContSet.Capsule.API
import CORALean.ContSet.LevelSet.API
import CORALean.ContSet.HPolytope.API
import CORALean.ContSet.VPolytope.API
import CORALean.ContSet.Conversion.API
import CORALean.ContSet.ConZonotope.API
import CORALean.ContSet.PolyZonotope.API
import CORALean.ContSet.ConPolyZono.API
import CORALean.ContSet.Taylm.API
import CORALean.ContSet.Zoo.API

/-!
# Set representations, collected

`ContSet` is the interface every representation instantiates; `InflatedContSet`
is what a float representation adds on top of its exact counterpart, beside it.
`EmptySet` and `Fullspace` are `∅` and the whole space as representations, as
CORA has them; `WithEmpty` wraps one for a result that may be `∅`, and
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
