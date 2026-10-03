# hybridDynamics/@transition

CORA methods of `hybridDynamics/@transition/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Transition`, `ParallelHybridAutomaton`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `convGuard` | float | [`Transition.convGuard`](../../../src/CORALean/HybridDynamics/Operations/TransitionConvGuard.lean), [`Transition.convGuard_guard_exact`](../../../src/CORALean/HybridDynamics/Theorems/TransitionConvGuardExact.lean) | route b — the `'polytope'` branch, generic over the float scalar: the guard becomes the stacked-rows intersection with the invariant, exact (`=`). The `'conZonotope'` branch and the conversion of a non-polytope guard are not modelled |
| `derivatives` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `eq` | out-of-scope | n/a — matlab-runtime |  |
| `eventFcn` | out-of-scope | n/a — matlab-runtime | ODE event callback |
| `guard2polytope` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `lift` | float | [`ParallelHybridAutomaton.liftTransition`](../../../src/CORALean/HybridDynamics/Parallel/Operations/LiftTransition.lean), [`ParallelHybridAutomaton.liftTransition_reset`](../../../src/CORALean/HybridDynamics/Parallel/Theorems/LiftTransitionReset.lean) | route b — generic over `Scalar 𝕋` with `ExactScalar 𝕋` (float instance), computable; `mergeFlows` is run at `Dyadic` in `Examples/RunnableFloat.lean` |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `synchronize` | — | — |  |
| `transition` | float | [`Transition.reset`](../../../src/CORALean/HybridDynamics/Definitions/Transition.lean), [`Transition.reset_image_subset`](../../../src/CORALean/HybridDynamics/Theorems/ResetImageSubset.lean) · float: [`Transition.jumpFloat`](../../../src/CORALean/HybridDynamics/Operations/JumpFloat.lean), [`Transition.jumpFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/JumpFloatOuter.lean) | the float reset image is `W Rg ⊕ {w}` at a float zonotope, `w` stored floats so no `Real.OfInterval` is needed |
