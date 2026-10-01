# contDynamics/@nonlinearSys

CORA methods of `contDynamics/@nonlinearSys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinearSys`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `eq` | out-of-scope | n/a — matlab-runtime |  |
| `falsify` | — | — |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `getfcn` | out-of-scope | n/a — matlab-runtime |  |
| `identify` | — | — |  |
| `initReach` | proved | [`NonlinearSys.linearize`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/Linearize.lean), [`NonlinearSys.linReachPoly`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachPoly.lean), [`NonlinearSys.Trajectory.linReachPoly_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachPolyOuter.lean) |  |
| `initReach_adaptive` | proved | [`NonlinearSys.adaptInit`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptInit.lean), [`NonlinearSys.adaptStep`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStep.lean), [`NonlinearSys.adaptStep_invariant`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptStepInvariant.lean) |  |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `linReach_adaptive` | proved | [`NonlinearSys.adaptLinPass`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptLinPass.lean), [`NonlinearSys.Trajectory.confinement_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ConfinementOfSubset.lean), [`NonlinearSys.reachSet_confinement_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetConfinementOfSubset.lean) | cora-issue — the same after-the-fact confinement check as `contDynamics/linReach`, which establishes nothing; CORALean takes confinement from an a priori ball about the step's start ([FINDINGS](../../../FINDINGS.md), "Confinement of a run to a linearization's region") |
| `linearize` | float | [`NonlinearSys.linearize`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/Linearize.lean), [`NonlinearSys.Trajectory.linearize`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/Linearize.lean), [`NonlinearSys.Trajectory.linearize_horizon`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinearizeHorizon.lean) · float: [`NonlinearSys.FloatModel.linearizeFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinearizeFloat.lean), [`NonlinearSys.FloatModel.linInputFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinInputFloat.lean), [`NonlinearSys.FloatModel.Encloses.linInputFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinInputFloatOuter.lean) | route a through a `FloatModel` of `f` (interval extensions of `f` and its Jacobian blocks, tied to `f` by `Encloses`); the remainder is first order in the deviation, not CORA's Hessian bound |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `nonlinearSys` | proved | [`NonlinearSys.toNonlinParam`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ToNonlinParam.lean), [`NonlinearSys.Trajectory.toNonlinParam`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/TrajectoryToNonlinParam.lean) | conversion to `NonlinParamSys`: every trajectory is one of the image |
| `post` | proved | [`NonlinearSys.relinTimeInterval`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinTimeInterval.lean), [`NonlinearSys.relinDeltaReach`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinDeltaReach.lean), [`NonlinearSys.Trajectory.relinTimeInterval_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinTimeIntervalOuter.lean), [`NonlinearSys.Trajectory.relinDeltaReach_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinDeltaReachOuter.lean) | a step runs in floats as `NonlinearSys.FloatModel.relinStepFloat` (`Encloses.relinStepFloat_outer`); `relinDeltaReach` is pending #1, so the row stays `proved` |
| `reachInner` | — | — |  |
| `reach_adaptive` | proved | [`NonlinearSys.adaptRun`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptRun.lean), [`NonlinearSys.relinReach`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinReach.lean), [`NonlinearSys.reachSet_subset_relinReach`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetSubsetRelinReach.lean), [`NonlinearSys.Trajectory.relinReach_evalOn`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachEvalOn.lean), [`NonlinearSys.Trajectory.relinReach_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachOuter.lean), [`NonlinearSys.Trajectory.relinReach_outer_inputSolution`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachOuterInputSolution.lean) | the re-linearization loop runs in floats as `NonlinearSys.FloatModel.reachFloat` (`Encloses.reachFloat_outer`, `relinRunFloat_outer`); `adaptRun` is pending #1, so the row stays `proved` |
| `simulate` | — | — |  |
| `taylor` | — | — |  |
