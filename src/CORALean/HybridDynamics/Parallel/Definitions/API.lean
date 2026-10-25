module

public import CORALean.Global.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.HybridDynamics.Parallel.Definitions.Lifting
public import CORALean.HybridDynamics.Parallel.Definitions.IsSelfBindFree
public import CORALean.HybridDynamics.Parallel.Definitions.ReachSetExact
public import CORALean.HybridDynamics.Parallel.Definitions.IsFlowLaw
public import CORALean.HybridDynamics.Parallel.Definitions.IsFlowLawConverse
public import CORALean.HybridDynamics.Parallel.Definitions.IsFeedthroughFree
public import CORALean.HybridDynamics.Parallel.Definitions.HasStateBound
public import CORALean.HybridDynamics.Parallel.Definitions.GlobalsDistinct
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Definitions.SyncLabels
public import CORALean.HybridDynamics.Parallel.Definitions.SyncLifting
public import CORALean.HybridDynamics.Parallel.Definitions.IsSyncRun

/-!
# What a parallel hybrid automaton means

`Lifting` is what lifting the components' sets into the product's spaces owes, a structure the
caller fills; `ReachSetExact` names what a `IsRun` quantifies over. `IsFlowLaw` is what a product's
flow must do to a stack for a parallel run to be a product run, `IsFlowLawConverse` the other way,
and `IsFeedthroughFree` CORA's check against algebraic loops, under which `mergeFlowsLinearSys` has
both. `ExactScalar` (`Global/Interfaces`) is the exact `0` and `1` that assembling a matrix out of
the components' asks of the scalar; `HasStateBound` and `IsSelfBindFree` are where that assembly,
`mergeFlows`, is `mergeFlowsLinearSys`. `LiftingExact` and `GlobalsDistinct` are the conditions
of the converse of `IsRun.toProduct`. `SyncLabels`, `SyncLifting` and `IsSyncRun` are
synchronization labels, their lifting and run semantics.
-/
