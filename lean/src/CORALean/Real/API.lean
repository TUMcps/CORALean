import CORALean.Real.MatSet.API
import CORALean.Real.ContSet.API
import CORALean.Real.ContDynamics.API

/-!
# Real arithmetic, collected

The specification layer: representations over ℝ, with exact arithmetic. Every
operation here is what its floating-point counterpart is judged against.

`ContDynamics` sits here too, not beside the two layers: an algorithm is written
against `OuterContSet` and never names a representation, so there is nothing for
`Float` to restate.
-/
