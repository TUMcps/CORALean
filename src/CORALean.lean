import CORALean.Global.API
import CORALean.Global.Float.API
import CORALean.ContSet.API
import CORALean.Specification.API
import CORALean.ContDynamics.API
import CORALean.HybridDynamics.API
import CORALean.NN.API
import CORALean.Examples.API

/-!
# CORALean

A Lean 4 formalization of [CORA](https://cora.in.tum.de).

Everything is developed twice: `Real` is the specification, exact over ℝ, and
`Float` recomputes it with directed rounding and proves the same enclosure by
composing with it. `Float` imports `Real`, never the reverse, so deleting every
`Float` directory leaves the specification standing.

Set representations in `ContSet`, algorithms over them in `ContDynamics`,
`HybridDynamics` and `NN`, and in `Specification` the step that makes any of it
a verification result: a check passed on a computed superset is passed by the
exact set it encloses.
-/
