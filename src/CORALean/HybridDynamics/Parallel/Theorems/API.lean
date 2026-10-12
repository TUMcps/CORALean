import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsMulVec
import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset
import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectory
import CORALean.HybridDynamics.Parallel.Theorems.RunToProduct
import CORALean.HybridDynamics.Parallel.Theorems.RunMemOfInvariant
import CORALean.HybridDynamics.Parallel.Theorems.ReachSetSubsetInvariant
import CORALean.HybridDynamics.Parallel.Theorems.ReachFloatOuter
import CORALean.HybridDynamics.Parallel.Theorems.ReachFloatCheckedEqSome
import CORALean.HybridDynamics.Parallel.Theorems.UnstackStack
import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack
import CORALean.HybridDynamics.Parallel.Theorems.StackApply
import CORALean.HybridDynamics.Parallel.Theorems.BlockProjApply
import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdA
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdb
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdAe
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdbe
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeComapBlockProjExact
import CORALean.HybridDynamics.Parallel.Theorems.BoxLifting
import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdFloatExact
import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectoryWith
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw
import CORALean.HybridDynamics.Parallel.Theorems.RunToProductWith
import CORALean.HybridDynamics.Parallel.Theorems.StayOfTrajectoryWith
import CORALean.HybridDynamics.Parallel.Theorems.RunOfProductWith
import CORALean.HybridDynamics.Parallel.Theorems.RunOfProduct
import CORALean.HybridDynamics.Parallel.Theorems.ReachSetProductWithEq
import CORALean.HybridDynamics.Parallel.Theorems.ReachSetProductEq
import CORALean.HybridDynamics.Parallel.Theorems.BoxLiftingExact
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddMulVec
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddFlowLaw
import CORALean.HybridDynamics.Parallel.Theorems.RunToProductAdd
import CORALean.HybridDynamics.Parallel.Theorems.RunOfProductAdd
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsSelfBindCounterexample
import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdValue
import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.ConZonotopeStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.ZonoLifting
import CORALean.HybridDynamics.Parallel.Theorems.ZonoLiftingExact
import CORALean.HybridDynamics.Parallel.Theorems.ConZonoLifting
import CORALean.HybridDynamics.Parallel.Theorems.ConZonoLiftingExact
import CORALean.HybridDynamics.Parallel.Theorems.LiftSyncTransitionReset
import CORALean.HybridDynamics.Parallel.Theorems.SyncRunToProduct
import CORALean.HybridDynamics.Parallel.Theorems.BoxSyncLifting
import CORALean.HybridDynamics.Parallel.Theorems.InvariantCutCoraCounterexample
import CORALean.HybridDynamics.Parallel.Theorems.MergeTransitionSetsCoraWrongTargetCounterexample

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
`mergeFlowsAdd` (no `SelfBindFree`) shares them. `MergeFlowsSelfBindCounterexample` shows
`SelfBindFree` cannot be dropped from `mergeFlows`. `SyncRunToProduct` is `Run.toProduct` with
synchronization labels.
-/
