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

**`reach` — the queue.** `HybridAutomaton.reachQueueFloat` is CORA's loop of `reach.m`, with its queue of
sets waiting for a location, its time bookkeeping and its branches
([`ReachQueueFloat`](../../../src/CORALean/HybridDynamics/Operations/ReachQueueFloat.lean),
[`ReachQueueLoopFloat`](../../../src/CORALean/HybridDynamics/Operations/ReachQueueLoopFloat.lean),
[`ReachQueueStepFloat`](../../../src/CORALean/HybridDynamics/Operations/ReachQueueStepFloat.lean)).

A pass takes `Reach.stepCount` steps of `Location.stayFloat` (stopped at the first set certified
disjoint from the invariant), lists the hits with `Location.potInt`, groups them with
`Location.guardGroups` and makes one entry per crossing with `Location.queueJumpFloat` (the box of
`zonoGirard` with the `'box'` basis, a hyperplane guard, the reset).

Outer:
[`HybridAutomaton.reachQueueFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/ReachQueueFloatOuter.lean),
from the loop
([`reachQueueLoopFloat_encloses`](../../../src/CORALean/HybridDynamics/Theorems/ReachQueueLoopFloatEncloses.lean)),
the pass
([`reachQueueStepFloat_encloses`](../../../src/CORALean/HybridDynamics/Theorems/ReachQueueStepFloatEncloses.lean)),
the stay and its window
([`stayFloat_outer_window`](../../../src/CORALean/HybridDynamics/Theorems/LocationStayFloatOuter.lean),
[`takeThrough`](../../../src/CORALean/Global/TakeThrough.lean)),
the groups
([`guardGroups_mem`](../../../src/CORALean/HybridDynamics/Theorems/GuardGroupsMem.lean)).

The crossing
([`queueJumpFloat_encloses`](../../../src/CORALean/HybridDynamics/Theorems/LocationQueueJumpFloatEncloses.lean),
[`dotProduct_of_hyperplane`](../../../src/CORALean/ContSet/HPolytope/Float/Theorems/HyperplaneSound.lean),
[`mem_queueSetsFloat_of_jump`](../../../src/CORALean/HybridDynamics/Theorems/LocationMemQueueSetsFloatOfJump.lean),
[`guardOrientFloat?_sound`](../../../src/CORALean/HybridDynamics/Theorems/LocationGuardOrientFloatSound.lean),
[`inHalfspace_sound`](../../../src/CORALean/ContSet/HPolytope/Float/Theorems/InHalfspaceSound.lean))
and the step count
([`stepCount_real`](../../../src/CORALean/ContDynamics/Reach/Theorems/StepCountReal.lean)).

Every run that
starts at `tStart` in the initial set and ends one step before `tFinal` ends in a time-interval set of
a branch of its end location, for the orthogonal basis `eye(n)` and no transition into `finalLoc`
(a stay is cut at whole steps, as CORA's `tStart:timeStep:tFinal`).

**`reach` — `checkFlow` in the queue.** `options.checkFlow`, default true as CORA: before the intersection
`Location.queueSetsFloat` filters the sets of a crossing with `Location.checkFlowFloat`, the normal
turned out of the invariant by `Location.guardOrientFloat?`, and the crossing is dropped when no set
is kept; the jump times keep the group's first and last set before the filter, as CORA's `minInd`,
`maxInd`. With it on, the runs of the theorem are those with positive dwell time at every jump
(`IsRunUntilDwell`): a set whose flow points strictly into the invariant is dropped, and a run that
jumps at once from a state on the guard is where it would go (the crossing lemma, `location.md`).
With it off, every run, as before.

Not modelled: the swap of a lone
hyperplane hit for the next time-point set (sound only for a flow that crosses the hyperplane at
that instant). Also not modelled: the specifications, the `pca` and `flow` bases, the guard methods
other than `zonoGirard`, and guards that are not a bare hyperplane (the pass then fails).

**`reach` — cora-issue account.** CORA's `aux_set_HA_inputs` (`postProcessing.m` l. 603-617) writes,
for a numeric `params.u`, `uloc{i} = repmat({params.u},numLoc,1);` where `uloc = repmat(...)` was
meant (the `params.U` branch and the simulate variants at l. 721-727 do it right). `i` is the
left-over index of the `params.U` loop, i.e. the last location when `params.U` is a cell (the
default), and the imaginary unit otherwise (an index error). With the default `U`, `uloc` has only
entry `numLoc` set, to a cell of `numLoc` copies of `u`, so `reach` gives the other locations
`params.u = []` and the last a cell instead of `u`. A user input `u` is not applied as given (read
from the source, not run). Formalized as the cell array entry by entry (`ulocCora`) beside the
intended one (`uloc`).


**`reach` — MATLAB run.** MATLAB R2024b, CORA v2026.1.0 (904a444): not run: witness not constructed in this pass (needs a reach, DAE, observer or hybrid-automaton setup).