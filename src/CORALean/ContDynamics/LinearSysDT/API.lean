module

public import CORALean.ContDynamics.LinearSysDT.Complexity.API
public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachExistsOptions
public import CORALean.ContDynamics.LinearSysDT.Definitions.IsConformDyn
public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachForallOptions
public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetExists
public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetForall
public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetRobust
public import CORALean.ContDynamics.LinearSysDT.Definitions.GO
public import CORALean.ContDynamics.LinearSysDT.Definitions.GOFloat
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInner
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerFloat
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerReduced
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachOrdersOptions
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.LinearSysDT.Instances
public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContDynamics.LinearSysDT.Operations.API
public import CORALean.ContDynamics.LinearSysDT.Theorems.API
public import CORALean.ContDynamics.LinearSysDT.Counterexamples.API
public import CORALean.ContDynamics.LinearSysDT.Definitions.ConsistentSet
public import CORALean.ContDynamics.LinearSysDT.Definitions.ExactUncertainSet
public import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveStripOptions
public import CORALean.ContDynamics.LinearSysDT.Definitions.DescriptorPredictSet
public import CORALean.ContDynamics.LinearSysDT.Definitions.MeasurementSet
public import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveIntervalState
public import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveIntervalStateFloat
public import CORALean.ContDynamics.LinearSysDT.Definitions.IntervalEstimateState
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachErrorSet
public import CORALean.ContDynamics.LinearSysDT.Definitions.HinfLmi
public import CORALean.ContDynamics.LinearSysDT.Definitions.FaultRadiusLmi
public import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmi
public import CORALean.ContDynamics.LinearSysDT.Definitions.DescriptorDecoupleRank
public import CORALean.ContDynamics.LinearSysDT.Definitions.FaultRadiusLmiGain
public import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmiGain
public import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmiPhi
public import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusStepPositive

/-!
# Discrete-time linear systems, collected

The system and what it denotes in `LinearSysDT`, reachability in `Operations`
at CORA's `options` in `ReachOptions` and its siblings, the set reachability
encloses in `ReachSet`, what a run of it owes in `ReachError` and the inner approximation
that buys in `ReachInner`, the guarantees in `Theorems`, how large the owed
error is in `Complexity/Space`, and in `Complexity/Time` what running it costs.

`ReachUnionExact` is the set `Reach` asks to be enclosed, every step up to the
horizon, and `Instances` is the instance itself.

`ReachErrorReduced`/`ReachInnerReduced` are the same pair with the error
reduced at every step, sound since it is *added* to the exact set.
`ReachErrorFloat`/`ReachInnerFloat` are the same pair for a run computed at a
float scalar; its inner approximation sits inside the *exact* `reachSet`.

`BackReachSetForall` is the run read backwards — the states every admissible
input carries into a target — and `BackReachForall` computes inside it.
`BackReachSetExists` is the other reading, *some* input suffices, and
`BackReachExists` encloses it: a sum, so both halves are outer at `Plus,
Mtimes`. `ReachErrorOrders`/`ReachErrorReducedOrders` are `ReachError`/
`ReachErrorReduced` at `Operations.reachOrders`'s per-step order sequence.
-/
