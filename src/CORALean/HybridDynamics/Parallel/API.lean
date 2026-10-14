module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton
public import CORALean.HybridDynamics.Parallel.Definitions.API
public import CORALean.HybridDynamics.Parallel.Operations.API
public import CORALean.HybridDynamics.Parallel.Theorems.API
public import CORALean.HybridDynamics.Parallel.Counterexamples.API

/-!
# Parallel hybrid automata, collected

CORA's `parallelHybridAutomaton`: components, each a `HybridAutomaton`, whose inputs are bound
to global inputs or to each other's states. A run is a tuple of component runs on one shared
time axis, `Stay` and `jump`; `locationProduct` builds the product location as a location of
the single automaton, and `Run.toProduct` says every parallel run is a run of it, so the
single automaton's outer reachable sets bound the parallel one's.

Linear flows only, as `Location` is; the product's invariant, input set and guards are lifted by a
`Lifting` the caller supplies, since `ContSet` has no product; `boxLifting` is one, boxes for
inputs and halfspace descriptions for invariants and guards. `Run.ofProduct` is the converse of
`Run.toProduct` under stated conditions, `mergeFlowsAdd` closes `SelfBindFree` at an exact sum,
`SyncRun` and `productSync` are synchronization labels (soundness direction), and `zonoLifting`,
`conZonoLifting` are `Lifting`s with zonotope inputs. Nonlinear flows, outputs and the labeled
converse are not here (#40).
-/
