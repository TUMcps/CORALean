# hybridDynamics/@hybridAutomaton

CORA methods of `hybridDynamics/@hybridAutomaton/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `HybridAutomaton`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `bestInitialMode` | — | — | R-CTSIM: ranks the modes by the continuous `simulate`, which calls `ode45` or `ode15s`, and `interp1` |
| `derivatives` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `dynamicsEncodingMILP` | out-of-scope | n/a — solver-dependent |  |
| `eq` | out-of-scope | n/a — matlab-runtime |  |
| `falsify` | out-of-scope | n/a — solver-dependent | optimisation and wall-clock search for a falsifying trajectory |
| `hybridAutomaton` | float | [`HybridAutomaton.IsRunOn.mem_of_isInvariantOn`](../../../src/CORALean/HybridDynamics/Theorems/IsRunOnOuter.lean), [`HybridAutomaton.IsRun.mem_of_isInvariant`](../../../src/CORALean/HybridDynamics/Theorems/IsRunOuter.lean), [`HybridAutomaton.isInvariant_of_enclosure`](../../../src/CORALean/HybridDynamics/Theorems/InvariantOfEnclosure.lean), [`HybridAutomaton.isInvariant_of_enclosure_cut`](../../../src/CORALean/HybridDynamics/Theorems/InvariantOfEnclosureCut.lean), [`HybridAutomaton`](../../../src/CORALean/HybridDynamics/HybridAutomaton.lean) | route b — the automaton, its runs and its invariants are generic over `Scalar 𝕋` and the location representations; instantiated at float in `Examples/ReachFloat.lean` |
| `identify` | out-of-scope | n/a — solver-dependent | result determined by clustering and decision-tree learning |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `reach` | float | [`HybridAutomaton.reachSetExact`](../../../src/CORALean/HybridDynamics/Definitions/ReachSetExact.lean), [`HybridAutomaton.reachLocationsExact`](../../../src/CORALean/HybridDynamics/Definitions/ReachSetExact.lean), [`HybridAutomaton.IsRun.reachSetExact_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetExactOuter.lean), [`HybridAutomaton.reachSetExact_subset_isInvariant`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetExactSubsetInvariant.lean), [`HybridAutomaton.IsRun.reachLocationsExact_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachLocationsExactOuter.lean) · float: [`HybridAutomaton.reachFloat`](../../../src/CORALean/HybridDynamics/Operations/ReachFloat.lean), [`HybridAutomaton.reachFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachFloatOuter.lean), [`HybridAutomaton.reachSetExact_subset_reachFloat`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetExactSubsetReachFloat.lean), [`HybridAutomaton.IsRunUntil`](../../../src/CORALean/HybridDynamics/Definitions/IsRunUntil.lean), [`HybridAutomaton.isRun_iff_exists_isRunUntil`](../../../src/CORALean/HybridDynamics/Theorems/IsRunIffExistsIsRunUntil.lean), [`HybridAutomaton.reachSetExact_eq_iUnion_isRunUntil`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetExactEqIUnionIsRunUntil.lean) | float side: zonotope states, halfspace guards and invariants; encloses every run lasting at most `tFinal` with at most `K` jumps (`IsRunUntil`, which is a `IsRun` with a duration bound). Each stay is taken over the whole `tFinal` rather than the time left, and the guard is met by the box method; run on the bouncing ball at `Dyadic 24` in `Examples/BouncingBallFloat.lean`. cora-issue — CORA's `aux_set_HA_inputs` writes `uloc{i} = ...` where `uloc = ...` was meant, so a numeric `params.u` is not applied to the locations as given; [`HybridAutomaton.ulocCora_counterexample`](../../../src/CORALean/HybridDynamics/Counterexamples/UlocCora.lean), over [`HybridAutomaton.ulocCora`](../../../src/CORALean/HybridDynamics/Counterexamples/UlocCora.lean) and [`HybridAutomaton.uloc`](../../../src/CORALean/HybridDynamics/Operations/Basic.lean). Details below. |
| `simulate` | — | — | R-CTSIM: simulates each location by the continuous `simulate`, which calls `ode45` or `ode15s` |
| `simulateRandom` | out-of-scope | n/a — random/sampling |  |
| `viewGraph` | out-of-scope | n/a — plotting/display |  |

## Details

**`reach` — cora-issue account.** CORA's `aux_set_HA_inputs` (`postProcessing.m` l. 603-617) writes,
for a numeric `params.u`, `uloc{i} = repmat({params.u},numLoc,1);` where `uloc = repmat(...)` was
meant (the `params.U` branch and the simulate variants at l. 721-727 do it right). `i` is the
left-over index of the `params.U` loop, i.e. the last location when `params.U` is a cell (the
default), and the imaginary unit otherwise (an index error). With the default `U`, `uloc` has only
entry `numLoc` set, to a cell of `numLoc` copies of `u`, so `reach` gives the other locations
`params.u = []` and the last a cell instead of `u`. A user input `u` is not applied as given (read
from the source, not run). Formalized as the cell array entry by entry (`ulocCora`) beside the
intended one (`uloc`).
