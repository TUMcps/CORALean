import CORALean.Global.ExactScalar
import CORALean.HybridDynamics.Parallel.Definitions.Lifting
import CORALean.HybridDynamics.Parallel.Definitions.SelfBindFree
import CORALean.HybridDynamics.Parallel.Definitions.ReachSet

/-!
# What a parallel hybrid automaton means

`ExactScalar` (`Global/ExactScalar`) is the exact `0` and `1` assembling a matrix out of the
components' asks of the scalar, `SelfBindFree` where that assembly is `A + B * C`, and
`Lifting` what lifting their sets into the product's space owes, a structure the caller fills.
`ReachSet` names what a `Run` quantifies over.
-/
