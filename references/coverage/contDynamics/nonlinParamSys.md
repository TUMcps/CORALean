# contDynamics/@nonlinParamSys

CORA methods of `contDynamics/@nonlinParamSys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinParamSys`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `estimateParameter` | out-of-scope | n/a — solver-dependent | result determined by `fmincon` |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `getfcn` | out-of-scope | n/a — matlab-runtime |  |
| `initReach` | proved | [`NonlinParamSys.WithSteps.reachUnion`](../../../src/CORALean/ContDynamics/NonlinParamSys/Operations/ReachUnion.lean), [`NonlinParamSys.WithSteps.reachUnion_outer`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ReachUnionOuter.lean), [`NonlinParamSys.WithSteps.reachUnionExact`](../../../src/CORALean/ContDynamics/NonlinParamSys/Definitions/ReachUnionExact.lean) | parameters lifted to states (`augment`), not CORA's parametric linearisation; the outer theorem is stated against the NonlinParamSys semantics (every `ConstTrajectory` with a parameter in `P`), not only the augmented system |
| `linearize` | — | — | not formalized: the `paramInt` interval branch reads the zonotope `zf` and the matrix zonotopes `zA`, `zB` off the decomposition `f = f₀ + ∑ pᵢ fᵢ` of `parametricDynamicFile`, which `NonlinParamSys` does not carry (its `f` is one function of `p`), and the `'linRem'` option adds `lin_error2dAB`; the numeric-`p` branch is `NonlinearSys.linearize` at fixed `p` |
| `nonlinParamSys` | proved | [`NonlinParamSys.toNonlinearSys`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ToNonlinearSys.lean), [`NonlinParamSys.Trajectory.toNonlinearSys`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/TrajectoryToNonlinearSys.lean) | conversion to `NonlinearSys`: every trajectory is one of the image |
| `post` | proved | [`NonlinParamSys.WithSteps.reachUnion`](../../../src/CORALean/ContDynamics/NonlinParamSys/Operations/ReachUnion.lean), [`NonlinParamSys.WithSteps.reachUnion_outer`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/ReachUnionOuter.lean), [`NonlinParamSys.WithSteps.reachUnionExact`](../../../src/CORALean/ContDynamics/NonlinParamSys/Definitions/ReachUnionExact.lean) | parameters lifted to states (`augment`), not CORA's parametric linearisation; the outer theorem is stated against the NonlinParamSys semantics (every `ConstTrajectory` with a parameter in `P`), not only the augmented system |
| `simulate` | — | — | R-CTSIM: calls `ode45` |
