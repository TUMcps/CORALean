# contDynamics/@nonlinearSysDT

CORA methods of `contDynamics/@nonlinearSysDT/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinearSysDT`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `computeGO` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `executeObserver` | — | — |  |
| `falsify` | out-of-scope | n/a — solver-dependent | optimisation and wall-clock search for a falsifying trajectory |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `identify` | — | — |  |
| `linReach` | proved | [`NonlinearSysDT.linearize`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Operations/Linearize.lean), [`NonlinearSysDT.confinement_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ConfinementOfSubset.lean), [`NonlinearSysDT.confinement_of_subset_on`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ConfinementOfSubsetOn.lean) |  |
| `nonlinearSysDT` | proved | [`NonlinearSysDT`](../../../src/CORALean/ContDynamics/NonlinearSysDT/NonlinearSysDT.lean), [`NonlinearSysDT.simulate_trajectory`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/SimulateTrajectory.lean) | the structure, and the theorem that the simulated sequence is a trajectory of it |
| `post` | proved | [`NonlinearSysDT.reach_outer`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ReachOuter.lean), [`NonlinearSysDT.reach_outer_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ReachOuterOfSubset.lean), [`NonlinearSysDT.reach_outer_on`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ReachOuterOn.lean) |  |
| `reach` | proved | [`NonlinearSysDT.reach`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Operations/Reach.lean), [`NonlinearSysDT.WithSteps.reachUnion`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Operations/ReachUnion.lean), [`NonlinearSysDT.reach_outer`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ReachOuter.lean), [`NonlinearSysDT.reach_outer_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ReachOuterOfSubset.lean), [`NonlinearSysDT.reach_outer_on`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ReachOuterOn.lean), [`NonlinearSysDT.WithSteps.reachUnion_outer`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/ReachUnionOuter.lean) |  |
| `simulate` | proved | [`NonlinearSysDT.simulate_mem_reach`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Theorems/SimulateMemReach.lean) |  |
