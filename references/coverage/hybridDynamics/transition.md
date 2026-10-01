# hybridDynamics/@transition

CORA methods of `hybridDynamics/@transition/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Transition`, `ParallelHybridAutomaton`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `convGuard` | — | — |  |
| `derivatives` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `eq` | — | — |  |
| `eventFcn` | — | — |  |
| `guard2polytope` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `lift` | float | [`ParallelHybridAutomaton.liftTransition`](../../../src/CORALean/HybridDynamics/Parallel/Operations/LiftTransition.lean), [`ParallelHybridAutomaton.liftTransition_reset`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/LiftTransitionReset.lean) | route b — generic over `Scalar 𝕋` with `ExactScalar 𝕋` (float instance), computable; `mergeFlows` is run at `Dyadic` in `Examples/RunnableFloat.lean` |
| `ne` | — | — |  |
| `synchronize` | — | — |  |
| `transition` | proved | [`Transition.reset`](../../../src/CORALean/HybridDynamics/Definitions/Transition.lean), [`Transition.reset_image_subset`](../../../src/CORALean/HybridDynamics/Theorems/ResetImageSubset.lean) |  |
