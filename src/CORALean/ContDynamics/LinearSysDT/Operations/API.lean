import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxFloat
import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxIn
import CORALean.ContDynamics.LinearSysDT.Operations.BackReachExists
import CORALean.ContDynamics.LinearSysDT.Operations.BackReachForall
import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReduced
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReducedOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachInnerRep
import CORALean.ContDynamics.LinearSysDT.Operations.ReachUnion
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStep
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStripBased

/-!
# What `LinearSysDT` computes

`Reach` holds every representation with `Plus` and `Reduce` at order `o`;
`ReachOrders` re-chooses the order at every step, `ReachHeld` is `reach` at
`𝕋 = ℝ` and one held input in closed form, and `Simulate` samples one run.
`ReachUnion` packages `reach`'s steps as `Reach`'s `SetUnion`.

`BackReachForall`/`BackReachExists` read a run backwards, against a matrix
inverse rather than the forward dynamics. `ReachError` and its `Reduced`,
`Orders` and `Float` variants accumulate what a run owes as a zonotope, each
one an algorithm rather than the `reach` it is measured against. `ReachInnerRep`
is the inner approximation at a representation.
-/
