import CORALean.ContSet.ContSet.API
import CORALean.ContSet.InflatedContSet.API
import CORALean.ContSet.Interval.API
import CORALean.ContSet.Zonotope.API
import CORALean.ContSet.HPolytope.API
import CORALean.ContSet.VPolytope.API
import CORALean.ContSet.Polytope.API
import CORALean.ContSet.ConZonotope.API

/-!
# Set representations, collected

`ContSet` is the interface every representation instantiates; then one directory
each, holding both arithmetic layers where a representation has both.
`InflatedContSet` is what a float representation adds on top of its exact
counterpart, so it sits beside them rather than inside either.

`HPolytope` and `VPolytope` describe the same sets, by halfspaces and by
vertices, and are separate representations because converting between them is
vertex enumeration. `ConZonotope` builds on two of the others: it is a zonotope
whose coefficients a halfspace description cuts down.
-/
