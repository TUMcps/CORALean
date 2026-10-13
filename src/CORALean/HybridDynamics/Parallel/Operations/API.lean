module

public import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
public import CORALean.HybridDynamics.Parallel.Operations.LiftTransition
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.LocationProduct
public import CORALean.HybridDynamics.Parallel.Operations.Product
public import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
public import CORALean.HybridDynamics.Parallel.Operations.ReachFloatChecked
public import CORALean.HybridDynamics.Parallel.Operations.Unstack
public import CORALean.HybridDynamics.Parallel.Operations.BlockProj
public import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProd
public import CORALean.HybridDynamics.Parallel.Operations.HPolytopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProdFloat
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsAdd
public import CORALean.HybridDynamics.Parallel.Operations.ProductWith
public import CORALean.HybridDynamics.Parallel.Operations.ProductAdd
public import CORALean.HybridDynamics.Parallel.Operations.SyncPick
public import CORALean.HybridDynamics.Parallel.Operations.LiftSyncTransition
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSetsCoraTarget
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSetsSync
public import CORALean.HybridDynamics.Parallel.Operations.ProductSync
public import CORALean.HybridDynamics.Parallel.Operations.ZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.ConZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.InvariantCutCora
public import CORALean.HybridDynamics.Parallel.Operations.InvariantCutDocumented
public import CORALean.HybridDynamics.Parallel.Operations.SimulateRandomTimesCora

/-!
# What a parallel hybrid automaton computes, collected

CORA's `locationProduct` and the three merges it is made of. `mergeFlows` is block diagonal in the
components' `A` with the state-bound inputs moved into it; `liftTransition` and
`mergeTransitionSets` lift each component's transitions, one by one; `mergeInvariants` and
`mergeInputSets` call the caller's `Lifting`. `locationProduct` assembles one location and
`product` the whole `HybridAutomaton`. `unstack` and `blockProj` read a block of the stacked
space; `Interval.stackProd` and `HPolytope.stackProd` are the Cartesian products a `Lifting` is
made of. `mergeFlowsAdd` sums where `mergeFlows` replaces, so needs no `SelfBindFree` (at a scalar
with an exact sum); `productWith` takes the flow as an argument and `product`, `productAdd` are
its two instances. `Zonotope.stackProd` and `ConZonotope.stackProd` are the Cartesian products for
the zonotope `Lifting`s. `SyncLabels.pick`, `liftSyncTransition`, `mergeTransitionSetsSync` and
`productSync` are synchronization labels. Linear flows only (#40).
-/
