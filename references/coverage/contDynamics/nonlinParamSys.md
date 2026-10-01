# contDynamics/@nonlinParamSys

CORA methods of `contDynamics/@nonlinParamSys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinParamSys`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `estimateParameter` | — | — |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `getfcn` | out-of-scope | n/a — matlab-runtime |  |
| `initReach` | proved | [`NonlinParamSys.WithSteps.reachUnion`](../../../src/CORALean/ContDynamics/NonlinParamSys/Operations/ReachUnion.lean), [`NonlinParamSys.WithSteps.reachUnion_outer`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ReachUnionOuter.lean), [`NonlinParamSys.WithSteps.reachUnionExact`](../../../src/CORALean/ContDynamics/NonlinParamSys/Definitions/ReachUnionExact.lean) | parameters lifted to states (`augment`), not CORA's parametric linearisation; the outer theorem is stated against the NonlinParamSys semantics (every `ConstTrajectory` with a parameter in `P`), not only the augmented system |
| `linearize` | — | — |  |
| `nonlinParamSys` | proved | [`NonlinParamSys.toNonlinearSys`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ToNonlinearSys.lean), [`NonlinParamSys.Trajectory.toNonlinearSys`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/TrajectoryToNonlinearSys.lean) | conversion to `NonlinearSys`: every trajectory is one of the image |
| `post` | proved | [`NonlinParamSys.WithSteps.reachUnion`](../../../src/CORALean/ContDynamics/NonlinParamSys/Operations/ReachUnion.lean), [`NonlinParamSys.WithSteps.reachUnion_outer`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ReachUnionOuter.lean), [`NonlinParamSys.WithSteps.reachUnionExact`](../../../src/CORALean/ContDynamics/NonlinParamSys/Definitions/ReachUnionExact.lean) | parameters lifted to states (`augment`), not CORA's parametric linearisation; the outer theorem is stated against the NonlinParamSys semantics (every `ConstTrajectory` with a parameter in `P`), not only the augmented system |
| `simulate` | — | — |  |
