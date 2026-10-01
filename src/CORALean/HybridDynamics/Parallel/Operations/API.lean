import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
import CORALean.HybridDynamics.Parallel.Operations.LiftTransition
import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets
import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
import CORALean.HybridDynamics.Parallel.Operations.LocationProduct
import CORALean.HybridDynamics.Parallel.Operations.Product

/-!
# What a parallel hybrid automaton computes, collected

CORA's `locationProduct` and the three merges it is made of. `mergeFlows` is block diagonal in
the components' `A` with the state-bound inputs moved into it; `liftTransition` and
`mergeTransitionSets` lift each component's transitions, one by one; `mergeInvariants` and
`mergeInputSets` call the caller's `Lifting`. `locationProduct` assembles one location and
`product` the whole `HybridAutomaton`. Linear flows only, and no synchronization labels (#40).
-/
