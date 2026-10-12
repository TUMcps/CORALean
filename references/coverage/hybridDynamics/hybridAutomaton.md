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
| `hybridAutomaton` | float | [`HybridAutomaton.RunOn.mem_of_invariantOn`](../../../src/CORALean/HybridDynamics/Theorems/RunOnOuter.lean), [`HybridAutomaton.Run.mem_of_invariant`](../../../src/CORALean/HybridDynamics/Theorems/RunOuter.lean), [`HybridAutomaton.invariant_of_enclosure`](../../../src/CORALean/HybridDynamics/Theorems/InvariantOfEnclosure.lean), [`HybridAutomaton.invariant_of_enclosure_cut`](../../../src/CORALean/HybridDynamics/Theorems/InvariantOfEnclosureCut.lean), [`HybridAutomaton`](../../../src/CORALean/HybridDynamics/HybridAutomaton.lean) | route b — the automaton, its runs and its invariants are generic over `Scalar 𝕋` and the location representations; instantiated at float in `Examples/ReachFloat.lean` |
| `identify` | out-of-scope | n/a — solver-dependent | result determined by clustering and decision-tree learning |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `reach` | float | [`HybridAutomaton.reachSet`](../../../src/CORALean/HybridDynamics/Definitions/ReachSet.lean), [`HybridAutomaton.reachLocations`](../../../src/CORALean/HybridDynamics/Definitions/ReachSet.lean), [`HybridAutomaton.Run.reachSet_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetOuter.lean), [`HybridAutomaton.reachSet_subset_invariant`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetSubsetInvariant.lean), [`HybridAutomaton.Run.reachLocations_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachLocationsOuter.lean) · float: [`HybridAutomaton.reachFloat`](../../../src/CORALean/HybridDynamics/Operations/ReachFloat.lean), [`HybridAutomaton.reachFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachFloatOuter.lean), [`HybridAutomaton.reachSet_subset_reachFloat`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetSubsetReachFloat.lean), [`HybridAutomaton.RunUntil`](../../../src/CORALean/HybridDynamics/Definitions/RunUntil.lean), [`HybridAutomaton.run_iff_exists_runUntil`](../../../src/CORALean/HybridDynamics/Theorems/RunIffExistsRunUntil.lean), [`HybridAutomaton.reachSet_eq_iUnion_runUntil`](../../../src/CORALean/HybridDynamics/Theorems/ReachSetEqIUnionRunUntil.lean) | float side: zonotope states, halfspace guards and invariants; encloses every run lasting at most `tFinal` with at most `K` jumps (`RunUntil`, which is a `Run` with a duration bound); each stay is taken over the whole `tFinal` rather than the time left, and the guard is met by the box method; run on the bouncing ball at `Dyadic 24` in `Examples/BouncingBallFloat.lean` ; cora-issue — `aux_set_HA_inputs` (`postProcessing.m:617`) writes `uloc{i} = repmat({params.u},numLoc,1)` for a numeric `params.u`, with `i` left over from the `params.U` loop (the last location, or `1i`, an index error, if `params.U` is numeric), so with the default cell `U` only the last location gets an input, a cell of `numLoc` copies of `u`, and the others `[]` (FINDINGS.md): [`HybridAutomaton.ulocCora_counterexample`](../../../src/CORALean/HybridDynamics/Theorems/UlocCoraCounterexample.lean), over [`HybridAutomaton.ulocCora`](../../../src/CORALean/HybridDynamics/Operations/UlocCora.lean) and [`HybridAutomaton.uloc`](../../../src/CORALean/HybridDynamics/Operations/Uloc.lean); read from the source, not run |
| `simulate` | — | — | R-CTSIM: simulates each location by the continuous `simulate`, which calls `ode45` or `ode15s` |
| `simulateRandom` | out-of-scope | n/a — random/sampling |  |
| `viewGraph` | out-of-scope | n/a — plotting/display |  |
