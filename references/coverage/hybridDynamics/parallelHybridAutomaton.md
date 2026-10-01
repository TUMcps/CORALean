# hybridDynamics/@parallelHybridAutomaton

CORA methods of `hybridDynamics/@parallelHybridAutomaton/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `ParallelHybridAutomaton`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `eq` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `locationProduct` | float | [`ParallelHybridAutomaton.locationProduct`](../../../src/CORALean/HybridDynamics/Parallel/Operations/LocationProduct.lean), [`ParallelHybridAutomaton.product`](../../../src/CORALean/HybridDynamics/Parallel/Operations/Product.lean), [`ParallelHybridAutomaton.Run.toProduct`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/RunToProduct.lean) | route b — generic over `Scalar 𝕋` with `ExactScalar 𝕋` (float instance), computable; `mergeFlows` is run at `Dyadic` in `Examples/RunnableFloat.lean`; soundness direction only: a parallel run is a run of the product |
| `mergeFlows` | float | [`ParallelHybridAutomaton.mergeFlows`](../../../src/CORALean/HybridDynamics/Parallel/Operations/MergeFlows.lean), [`ParallelHybridAutomaton.mergeFlows_mulVec`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/MergeFlowsMulVec.lean) | route b — generic over `Scalar 𝕋` with `ExactScalar 𝕋` (float instance), computable; `mergeFlows` is run at `Dyadic` in `Examples/RunnableFloat.lean` |
| `mergeInvariants` | — | — |  |
| `mergeTransitionSets` | float | [`ParallelHybridAutomaton.mergeTransitionSets`](../../../src/CORALean/HybridDynamics/Parallel/Operations/MergeTransitionSets.lean), [`ParallelHybridAutomaton.liftTransition`](../../../src/CORALean/HybridDynamics/Parallel/Operations/LiftTransition.lean), [`ParallelHybridAutomaton.liftTransition_reset`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/LiftTransitionReset.lean), [`ParallelHybridAutomaton.Run.toProduct`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/RunToProduct.lean) | route b — generic over `Scalar 𝕋` with `ExactScalar 𝕋` (float instance), computable; `mergeFlows` is run at `Dyadic` in `Examples/RunnableFloat.lean`; soundness direction only: a parallel run is a run of the product |
| `ne` | — | — |  |
| `parallelHybridAutomaton` | float | [`ParallelHybridAutomaton.Run.mem_of_invariant`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/RunMemOfInvariant.lean), [`ParallelHybridAutomaton`](../../../src/CORALean/HybridDynamics/Parallel/ParallelHybridAutomaton.lean) | route b — generic over `Scalar 𝕋` with `ExactScalar 𝕋` (float instance), computable; `mergeFlows` is run at `Dyadic` in `Examples/RunnableFloat.lean` |
| `reach` | proved | [`ParallelHybridAutomaton.reachSet`](../../../src/CORALean/HybridDynamics/Parallel/Definitions/ReachSet.lean), [`ParallelHybridAutomaton.reachSet_subset_invariant`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/ReachSetSubsetInvariant.lean) |  |
| `simulate` | — | — |  |
| `simulateRandom` | out-of-scope | n/a — random/sampling |  |
