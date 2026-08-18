import CORALean.Arithmetic.Real.ContSet.Interval.Instance
import CORALean.Arithmetic.Real.ContSet.Zonotope.Instance
import CORALean.Arithmetic.Real.ContDynamics.LinearSysDT.Theorems

/-!
# Real arithmetic, collected

The specification layer: representations over ℝ, with exact arithmetic. Every
operation here is what its floating-point counterpart is judged against.

One import per representation, and the `Theorems` file of each, so importing
this brings the guarantees along with the definitions.

`ContDynamics` sits here too, not beside the two layers: an algorithm is written
against `OuterContSet` and never names a representation, so there is nothing for
`Float` to restate.
-/
