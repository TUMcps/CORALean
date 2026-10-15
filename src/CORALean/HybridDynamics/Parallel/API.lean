module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton
public import CORALean.HybridDynamics.Parallel.Definitions.API
public import CORALean.HybridDynamics.Parallel.Operations.API
public import CORALean.HybridDynamics.Parallel.Theorems.API
public import CORALean.HybridDynamics.Parallel.Counterexamples.API

/-!
# Parallel hybrid automata, collected

CORA's `parallelHybridAutomaton`: components, each a `HybridAutomaton` whose locations flow by
their whole linear equation, whose inputs are bound to global inputs or to each other's outputs.
A run is a tuple of component runs on one shared time axis, `IsStay` and `jump`; `locationProduct`
builds the product location as a location of the single automaton, its flow
`mergeFlowsLinearSys`, and `IsRun.toProduct` says every parallel run is a run of it, so the single
automaton's outer reachable sets bound the parallel one's.

Linear flows only, as `Location` is; the product's invariant, input, disturbance and guard sets
are lifted by a `Lifting` the caller supplies, since `ContSet` has no product; `boxLifting`,
`zonoLifting` and `conZonoLifting` are three. `IsRun.ofProduct` is the converse of
`IsRun.toProduct` under stated conditions; `mergeFlows` is the merge assembled exactly at a float
scalar, which the float reach runs; `IsSyncRun` and `productSync` are synchronization labels
(soundness direction). Nonlinear flows and the labeled converse are not here (#40).
-/
