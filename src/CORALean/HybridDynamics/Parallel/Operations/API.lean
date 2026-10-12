import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
import CORALean.HybridDynamics.Parallel.Operations.LiftTransition
import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets
import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
import CORALean.HybridDynamics.Parallel.Operations.LocationProduct
import CORALean.HybridDynamics.Parallel.Operations.Product
import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
import CORALean.HybridDynamics.Parallel.Operations.ReachFloatChecked
import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
import CORALean.HybridDynamics.Parallel.Operations.Unstack
import CORALean.HybridDynamics.Parallel.Operations.BlockProj
import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProd
import CORALean.HybridDynamics.Parallel.Operations.HPolytopeStackProd
import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProdFloat
import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsAdd
import CORALean.HybridDynamics.Parallel.Operations.ProductWith
import CORALean.HybridDynamics.Parallel.Operations.ProductAdd
import CORALean.HybridDynamics.Parallel.Operations.SyncPick
import CORALean.HybridDynamics.Parallel.Operations.LiftSyncTransition
import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSetsCoraTarget
import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSetsSync
import CORALean.HybridDynamics.Parallel.Operations.ProductSync
import CORALean.HybridDynamics.Parallel.Operations.ZonotopeStackProd
import CORALean.HybridDynamics.Parallel.Operations.ConZonotopeStackProd
import CORALean.HybridDynamics.Parallel.Operations.InvariantCutCora
import CORALean.HybridDynamics.Parallel.Operations.InvariantCutDocumented

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
