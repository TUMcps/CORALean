import CORALean.ContSet.ContSet.API
import CORALean.ContSet.InflatedContSet.API
import CORALean.ContSet.Interval.API
import CORALean.ContSet.Zonotope.API
import CORALean.ContSet.Ellipsoid.API
import CORALean.ContSet.HPolytope.API
import CORALean.ContSet.VPolytope.API
import CORALean.ContSet.Conversion.API
import CORALean.ContSet.ConZonotope.API
import CORALean.ContSet.PolyZonotope.API
import CORALean.ContSet.ConPolyZono.API

/-!
# Set representations, collected

`ContSet` is the interface every representation instantiates; then one directory
each, holding both arithmetic layers where a representation has both.
`InflatedContSet` is what a float representation adds on top of its exact
counterpart, so it sits beside them rather than inside either.

`Ellipsoid` is the one representation whose support function is closed form in
every direction at once, which is what makes the conversions out of it tight
without a linear program.

`HPolytope` and `VPolytope` describe the same sets, by halfspaces and by
vertices, and are separate representations because converting between them is
vertex enumeration. `ConZonotope` builds on two of the others: it is a zonotope
whose coefficients a halfspace description cuts down. `PolyZonotope` is the
first representation here that need not be convex, and `ConPolyZono` builds on
it the same way `ConZonotope` builds on `Zonotope` — with the difference that
its constraints are polynomial in the factors and so cannot be a polytope.
Neither of the two has a float layer yet.

Two of the six intersect exactly, and they are exactly the two constrained
ones. That is not a coincidence: an intersection is a constraint, and a
representation that cannot carry one has to enclose it.
-/
