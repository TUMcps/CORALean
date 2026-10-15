module

public import CORALean.HybridDynamics.Parallel.Operations.BoxLifting
public import CORALean.HybridDynamics.Parallel.Operations.BoxSyncLifting
public import CORALean.HybridDynamics.Parallel.Operations.ConZonoLifting
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
public import CORALean.HybridDynamics.Parallel.Operations.LiftTransition
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeDistSets
public import CORALean.HybridDynamics.Parallel.Operations.SelectGlobal
public import CORALean.HybridDynamics.Parallel.Operations.LocationProduct
public import CORALean.HybridDynamics.Parallel.Operations.Product
public import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
public import CORALean.HybridDynamics.Parallel.Operations.ReachFloatChecked
public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.HybridDynamics.Parallel.Operations.BlockProj
public import CORALean.HybridDynamics.Parallel.Operations.HPolytopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProdFloat
public import CORALean.HybridDynamics.Parallel.Operations.ProductWith
public import CORALean.HybridDynamics.Parallel.Operations.SyncPick
public import CORALean.HybridDynamics.Parallel.Operations.LiftSyncTransition
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSetsSync
public import CORALean.HybridDynamics.Parallel.Operations.ProductSync
public import CORALean.HybridDynamics.Parallel.Operations.ZonoLifting
public import CORALean.HybridDynamics.Parallel.Operations.ZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.ConZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.InvariantCutDocumented
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsLinearSys

/-!
# What a parallel hybrid automaton computes, collected

CORA's `locationProduct` and the merges it is made of. `mergeFlowsLinearSys` is CORA's
`aux_mergeFlowsLinearSys`: the components' whole equations as one, inputs bound to outputs moved
into its `A`, `B` and `c`; `mergeFlows` is the same assembled without arithmetic at state-bound
components, for a float scalar. `liftTransition` and `mergeTransitionSets` lift each component's
transitions, one by one; `mergeInvariants`, `mergeInputSets` and `mergeDistSets` call the caller's
`Lifting`, `selectGlobal` reading the global inputs off the components' stacked inputs.
`locationProduct` assembles one location and `product` the whole `HybridAutomaton`; `productWith`
takes the flow and its sets as arguments. `unstack` and `blockProj` read a block of the stacked
space; `Interval.stackProd`, `HPolytope.stackProd`, `Zonotope.stackProd` and
`ConZonotope.stackProd` are the Cartesian products a `Lifting` is made of. `SyncLabels.pick`,
`liftSyncTransition`, `mergeTransitionSetsSync` and `productSync` are synchronization labels.
Linear flows only (#40).
-/
