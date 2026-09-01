import CORALean.Global.API
import CORALean.Global.Float.API
import CORALean.ContSet.API
import CORALean.ContDynamics.API

/-!
# CORALean

A Lean 4 formalization of [CORA](https://cora.in.tum.de).

Everything is developed twice: `Real` is the specification, exact over ℝ, and
`Float` recomputes it with directed rounding and proves the same enclosure by
composing with it. `Float` imports `Real`, never the reverse, so deleting every
`Float` directory leaves the specification standing.
-/
