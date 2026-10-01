# hybridDynamics/@hybridAutomaton

CORA methods of `hybridDynamics/@hybridAutomaton/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `HybridAutomaton`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `bestInitialMode` | — | — |  |
| `derivatives` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `dynamicsEncodingMILP` | out-of-scope | n/a — solver-dependent |  |
| `eq` | — | — |  |
| `falsify` | — | — |  |
| `hybridAutomaton` | float | [`HybridAutomaton.RunOn.mem_of_invariantOn`](../../../src/CORALean/HybridDynamics/Theorems/RunOnOuter.lean), [`HybridAutomaton.Run.mem_of_invariant`](../../../src/CORALean/HybridDynamics/Theorems/RunOuter.lean), [`HybridAutomaton.invariant_of_enclosure`](../../../src/CORALean/HybridDynamics/Theorems/InvariantOfEnclosure.lean), [`HybridAutomaton.invariant_of_enclosure_cut`](../../../src/CORALean/HybridDynamics/Theorems/InvariantOfEnclosureCut.lean), [`HybridAutomaton`](../../../src/CORALean/HybridDynamics/HybridAutomaton.lean) | route b — the automaton, its runs and its invariants are generic over `Scalar 𝕋` and the location representations; instantiated at float in `Examples/ReachFloat.lean` |
| `identify` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `ne` | — | — |  |
| `reach` | proved | [`HybridAutomaton.reachSet`](../../../src/CORALean/HybridDynamics/Definitions/ReachSet.lean), [`HybridAutomaton.reachLocations`](../../../src/CORALean/HybridDynamics/Definitions/ReachSet.lean), [`HybridAutomaton.Run.reachSet_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetOuter.lean), [`HybridAutomaton.reachSet_subset_invariant`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetSubsetInvariant.lean), [`HybridAutomaton.Run.reachLocations_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachLocationsOuter.lean) |  |
| `simulate` | — | — |  |
| `simulateRandom` | out-of-scope | n/a — random/sampling |  |
| `viewGraph` | out-of-scope | n/a — plotting/display |  |
