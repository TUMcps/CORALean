import CORALean.ContSet.ContSet.API
import CORALean.ContSet.InflatedContSet.API
import CORALean.ContSet.Interval.API
import CORALean.ContSet.Zonotope.API

/-!
# Set representations, collected

`ContSet` first: the interface every representation instantiates, denoting a set
over ℝ whichever scalar the representation computes in. Then one directory per
representation, each holding both layers.

`InflatedContSet` is what a float representation adds to its exact counterpart,
so it sits beside them rather than inside either.
-/
