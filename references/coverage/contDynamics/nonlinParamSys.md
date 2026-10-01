# contDynamics/@nonlinParamSys

CORA methods of `contDynamics/@nonlinParamSys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinParamSys`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `estimateParameter` | — | — |  |
| `getPrintSystemInfo` | — | — |  |
| `getfcn` | out-of-scope | n/a — matlab-runtime |  |
| `initReach` | — | — |  |
| `linearize` | — | — |  |
| `nonlinParamSys` | proved | [`NonlinParamSys.toNonlinearSys`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ToNonlinearSys.lean), [`NonlinParamSys.Trajectory.toNonlinearSys`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/TrajectoryToNonlinearSys.lean) | conversion to `NonlinearSys`: every trajectory is one of the image |
| `post` | — | — |  |
| `simulate` | — | — |  |
