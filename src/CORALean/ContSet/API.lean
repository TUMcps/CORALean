import CORALean.ContSet.ContSet.API
import CORALean.ContSet.InflatedContSet.API
import CORALean.ContSet.Interval.API
import CORALean.ContSet.Zonotope.API

/-!
# Set representations, collected

`ContSet` is the interface every representation instantiates; then one directory
per representation, each holding both layers. `InflatedContSet` is what a float
representation adds on top of its exact counterpart, so it sits beside them
rather than inside either.
-/
