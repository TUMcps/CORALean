import CORALean.ContDynamics.LinearSysDT.Operations.BackReachExists
import CORALean.ContDynamics.LinearSysDT.Operations.BackReachForall
import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGO
import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGOFloat
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReduced
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReducedOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.ReachInnerRep
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachUnion
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStep
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStripBased
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStepFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStripBasedFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ErrMatFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagationFloat
import CORALean.ContDynamics.LinearSysDT.Operations.IntersectStripSeqFloat
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxFloat
import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxIn
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStep
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalState
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveInterval
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStateFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStepFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoA1D
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoB1D
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoA
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoB
import CORALean.ContDynamics.LinearSysDT.Operations.Identify
import CORALean.ContDynamics.LinearSysDT.Operations.IdentifyCandidate
import CORALean.ContDynamics.LinearSysDT.Operations.ToLinearSys
import CORALean.ContDynamics.LinearSysDT.Operations.NominalState
import CORALean.ContDynamics.LinearSysDT.Operations.ConformReach
import CORALean.ContDynamics.LinearSysDT.Operations.ConformAdd
import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimateStep
import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimateState
import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimate
import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserver
import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverCoord
import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverTransformed
import CORALean.ContDynamics.LinearSysDT.Operations.ObserveDescriptorLPV
import CORALean.ContDynamics.LinearSysDT.Operations.GlmReach
import CORALean.ContDynamics.LinearSysDT.Operations.GlmReachBox

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
