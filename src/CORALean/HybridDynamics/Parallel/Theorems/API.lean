module

public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsMulVec
public import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset
public import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectory
public import CORALean.HybridDynamics.Parallel.Theorems.RunToProduct
public import CORALean.HybridDynamics.Parallel.Theorems.RunMemOfInvariant
public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetSubsetInvariant
public import CORALean.HybridDynamics.Parallel.Theorems.ReachFloatOuter
public import CORALean.HybridDynamics.Parallel.Theorems.ReachFloatCheckedEqSome
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack
public import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdA
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdb
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdAe
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdbe
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdFloatExact
public import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw
public import CORALean.HybridDynamics.Parallel.Theorems.RunToProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.StayOfTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.RunOfProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.RunOfProduct
public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetProductWithEq
public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetProductEq
public import CORALean.HybridDynamics.Parallel.Theorems.BoxLiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddMulVec
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddFlowLaw
public import CORALean.HybridDynamics.Parallel.Theorems.RunToProductAdd
public import CORALean.HybridDynamics.Parallel.Theorems.RunOfProductAdd
public import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdValue
public import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.ConZonotopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.ZonoLiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.ConZonoLiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.LiftSyncTransitionReset
public import CORALean.HybridDynamics.Parallel.Theorems.SyncRunToProduct
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlow

/-!
# What a parallel hybrid automaton guarantees, collected

`MergeFlowsMulVec` and `LiftTransitionReset` are the two identities the product's flow and jump
are read through; `StayTrajectory` takes a shared stay to a stay of the product and `RunToProduct`
a run to a run, by induction. `RunMemOfInvariant` and `ReachSetSubsetInvariant` are the single
automaton's outer-approximation theorems, stated against the parallel one. `StackUnstack` and its
neighbours relate `stack` to `unstack`; `IntervalStackProdExact` and `HPolytopeStackProdExact` say
the two Cartesian products are exact, `HPolytopeComapBlockProjExact` the guard's lift.
`BoxLifting` is the first concrete `Lifting`: boxes for inputs and halfspace descriptions for
invariants and guards; `ZonoLifting` and `ConZonoLifting` put the inputs in a zonotope or a
constrained zonotope instead, and `BoxSyncLifting` adds the guard conjunction that synchronized
transitions need. `Run.ofProduct` is the converse of `Run.toProduct` and `reachSet_product_eq` the
equality of reachable sets they give, under `Lifting.Exact`, `GlobalsDistinct` and
`InputsGlobalOnly`; all of them are proved once for any flow with `FlowLaw` (`...With`), so that
`mergeFlowsAdd` (no `SelfBindFree`) shares them. `MergeFlowsSelfBind` shows
`SelfBindFree` cannot be dropped from `mergeFlows`. `SyncRunToProduct` is `Run.toProduct` with
synchronization labels.
-/
