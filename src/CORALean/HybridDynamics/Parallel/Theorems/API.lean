module

public import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset
public import CORALean.HybridDynamics.Parallel.Theorems.IsStayTrajectory
public import CORALean.HybridDynamics.Parallel.Theorems.IsRunToProduct
public import CORALean.HybridDynamics.Parallel.Theorems.IsRunMemOfInvariant
public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetExactSubsetInvariant
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
public import CORALean.HybridDynamics.Parallel.Theorems.IsStayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw
public import CORALean.HybridDynamics.Parallel.Theorems.IsRunToProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.IsStayOfTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.IsRunOfProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.IsRunOfProduct
public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetExactProductWithEq
public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetExactProductEq
public import CORALean.HybridDynamics.Parallel.Theorems.BoxLiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdValue
public import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.ConZonotopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.ZonoLiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.ConZonoLiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.LiftSyncTransitionReset
public import CORALean.HybridDynamics.Parallel.Theorems.IsSyncRunToProduct
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlow
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlowLaw
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlowLawConverse
public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVec
public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVecStack
public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVecOfDistinct

/-!
# What a parallel hybrid automaton guarantees, collected

`MergeFlowsLinearSysFlow` is the identity the product's flow is read through, its merged right-hand
side being every component's own; `MergeFlowsLinearSysFlowLaw` and `...Converse` make it the flow
laws, `MergeFlowsFlowLaw` the same for the exact `mergeFlows`. `LiftTransitionReset` is the jump's
identity. `StayTrajectoryWith` takes a shared stay to a stay of the product and
`RunToProductWith` a run to a run, by induction, for any flow with the flow law; `RunToProduct` is
the product's. `RunMemOfInvariant` and `ReachSetExactSubsetInvariant` are the single automaton's
outer-approximation theorems, stated against the parallel one. `StackUnstack` and its neighbours
relate `stack` to `unstack`, the `…StackProdExact` say the Cartesian products are exact.
`BoxLifting`, `ZonoLifting` and `ConZonoLifting` are `Lifting`s, exact (`…LiftingExact`) where no
global input feeds two inputs (`SelectGlobal…`); `BoxSyncLifting` adds the guard conjunction that
synchronized transitions need. `IsRun.ofProduct` is the converse of `IsRun.toProduct` and
`reachSetExact_product_eq` the equality of reachable sets they give, under `Lifting.Exact`,
`GlobalsDistinct` and nonempty input sets. `SyncRunToProduct` is `IsRun.toProduct` with
synchronization labels; `ReachFloatOuter` the float reach's soundness.
-/
