module

public import CORALean.Global.ExactScalar
public import CORALean.HybridDynamics.Parallel.Definitions.Lifting
public import CORALean.HybridDynamics.Parallel.Definitions.SelfBindFree
public import CORALean.HybridDynamics.Parallel.Definitions.ReachSet
public import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw
public import CORALean.HybridDynamics.Parallel.Definitions.FlowLawConverse
public import CORALean.HybridDynamics.Parallel.Definitions.FeedthroughFree
public import CORALean.HybridDynamics.Parallel.Definitions.StateBound
public import CORALean.HybridDynamics.Parallel.Definitions.GlobalsDistinct
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Definitions.SyncLabels
public import CORALean.HybridDynamics.Parallel.Definitions.SyncLifting
public import CORALean.HybridDynamics.Parallel.Definitions.IsSyncRun

/-!
# What a parallel hybrid automaton means

`Lifting` is what lifting the components' sets into the product's spaces owes, a structure the
caller fills; `ReachSet` names what a `IsRun` quantifies over. `FlowLaw` is what a product's flow
must do to a stack for a parallel run to be a product run, `FlowLawConverse` the other way, and
`FeedthroughFree` CORA's check against algebraic loops, under which `mergeFlowsLinearSys` has
both. `ExactScalar` (`Global/ExactScalar`) is the exact `0` and `1` that assembling a matrix out of
the components' asks of the scalar; `StateBound` and `SelfBindFree` are where that assembly,
`mergeFlows`, is `mergeFlowsLinearSys`. `LiftingExact` and `GlobalsDistinct` are the conditions
of the converse of `IsRun.toProduct`. `SyncLabels`, `SyncLifting` and `IsSyncRun` are
synchronization labels, their lifting and run semantics.
-/
