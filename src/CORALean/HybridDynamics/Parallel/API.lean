import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton
import CORALean.HybridDynamics.Parallel.Definitions.API
import CORALean.HybridDynamics.Parallel.Operations.API
import CORALean.HybridDynamics.Parallel.Theorems.API

/-!
# Parallel hybrid automata, collected

CORA's `parallelHybridAutomaton`: components, each a `HybridAutomaton`, whose inputs are bound
to global inputs or to each other's states. A run is a tuple of component runs on one shared
time axis, `Stay` and `jump`; `locationProduct` builds the product location as a location of
the single automaton, and `Run.toProduct` says every parallel run is a run of it, so the
single automaton's outer reachable sets bound the parallel one's.

Linear flows only, as `Location` is; the product's invariant, input set and guards are lifted
by a `Lifting` the caller supplies, since `ContSet` has no product; `boxLifting` is one, boxes
for inputs and halfspace descriptions for invariants and guards. The converse of
`Run.toProduct`, synchronization labels and nonlinear flows are not here (#40).
-/
