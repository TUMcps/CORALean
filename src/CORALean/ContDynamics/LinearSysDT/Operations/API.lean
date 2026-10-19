module

public import CORALean.ContDynamics.LinearSysDT.Operations.BackReachExists
public import CORALean.ContDynamics.LinearSysDT.Operations.BackReachForall
public import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGO
public import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGOFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReduced
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReducedOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachInnerRep
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachSetBound
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachSetWitness
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStep
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStripBased
public import CORALean.ContDynamics.LinearSysDT.Operations.ErrMatFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagationFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxIn
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalState
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveInterval
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoA1D
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoB1D
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoA
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoB
public import CORALean.ContDynamics.LinearSysDT.Operations.Identify
public import CORALean.ContDynamics.LinearSysDT.Operations.OfABc
public import CORALean.ContDynamics.LinearSysDT.Operations.IdentifyCandidate
public import CORALean.ContDynamics.LinearSysDT.Operations.ToLinearSys
public import CORALean.ContDynamics.LinearSysDT.Operations.NominalState
public import CORALean.ContDynamics.LinearSysDT.Operations.ConformReach
public import CORALean.ContDynamics.LinearSysDT.Operations.ConformAdd
public import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimateStep
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimateState
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimate
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserver
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverCoord
public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverTransformed
public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveDescriptorLPV
public import CORALean.ContDynamics.LinearSysDT.Operations.GlmReach
public import CORALean.ContDynamics.LinearSysDT.Operations.GlmReachBox
public import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
public import CORALean.ContDynamics.LinearSysDT.Operations.CanonicalFloat

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
is the inner approximation at a representation. `ReachLTVCora` is CORA's loop
for a time-varying system, as printed.
-/
