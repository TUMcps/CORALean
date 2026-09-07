import CORALean.Global.API
import CORALean.Global.Float.API
import CORALean.ContSet.API
import CORALean.Specification.API
import CORALean.ContDynamics.API
import CORALean.HybridDynamics.API
import CORALean.NN.API

/-!
# CORALean

A Lean 4 formalization of [CORA](https://cora.in.tum.de).

The arithmetic is developed twice: `Real` is the specification, exact over ℝ,
and `Float` recomputes it with directed rounding and proves the same enclosure
by composing with it. `Float` imports `Real`, never the reverse, so deleting
every `Float` directory leaves the specification standing. What is parametric
in the representation belongs to neither and sits in `CORALean` itself: an
algorithm is written once and runs at either layer.

Set representations in `ContSet`, algorithms over them in `ContDynamics`,
`HybridDynamics` and `NN`, and in `Specification` the step that makes any of it
a verification result: a check passed on a computed superset is passed by the
exact set it encloses.

`Examples/` is deliberately not collected here, nor is `Demo`: both are targets
of their own, so the library holds the development and nothing that uses it.
-/
