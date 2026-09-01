import CORALean.ContSet.ContSet.API
import CORALean.ContSet.InflatedContSet.API
import CORALean.ContSet.Interval.API
import CORALean.ContSet.Zonotope.API
import CORALean.ContSet.Polytope.API
import CORALean.ContSet.ConZonotope.API

/-!
# Set representations, collected

`ContSet` is the interface every representation instantiates; then one directory
each, holding both arithmetic layers where a representation has both.
`InflatedContSet` is what a float representation adds on top of its exact
counterpart, so it sits beside them rather than inside either.

`Polytope` and `ConZonotope` build on the ones above them: a constrained
zonotope is a zonotope whose coefficients a polytope cuts down.
-/
