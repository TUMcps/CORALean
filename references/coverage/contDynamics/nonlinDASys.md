# contDynamics/@nonlinDASys

CORA methods of `contDynamics/@nonlinDASys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinDASys`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `consistentInitialState` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `getfcn` | out-of-scope | n/a — matlab-runtime |  |
| `initReach` | — | — |  |
| `linReach` | — | — |  |
| `linReach_adaptive` | — | — |  |
| `nonlinDASys` | proved | [`NonlinDASys`](../../../src/CORALean/ContDynamics/NonlinDASys/NonlinDASys.lean), [`NonlinDASys.Trajectory`](../../../src/CORALean/ContDynamics/NonlinDASys/NonlinDASys.lean), [`NonlinDASys.Trajectory.toNonlinearSys`](../../../src/CORALean/ContDynamics/NonlinDASys/Theorems/TrajectoryToNonlinearSys.lean), [`NonlinearSys.Trajectory.toNonlinDASys`](../../../src/CORALean/ContDynamics/NonlinDASys/Theorems/TrajectoryOfNonlinearSys.lean), [`NonlinDASys.exists_localReduction`](../../../src/CORALean/ContDynamics/NonlinDASys/Theorems/ExistsLocalReduction.lean) | `f`, `g` over ℝ, no output equation. Index 1 (`∂g/∂y` invertible, [`NonlinDASys.Index1`](../../../src/CORALean/ContDynamics/NonlinDASys/Definitions/Index1.lean)) is a hypothesis, not a field; globally the algebraic variable is eliminated through a caller-supplied [`NonlinDASys.ReducedModel`](../../../src/CORALean/ContDynamics/NonlinDASys/Definitions/ReducedModel.lean) (`g(x, h(x,u), u) = 0` and the only solution), whose trajectories are exactly those of the reduced ODE; `exists_localReduction` gives such an `h` only locally, by the implicit function theorem |
| `outputSet` | — | — |  |
| `post` | proved | [`NonlinDASys.WithSteps.reachUnion`](../../../src/CORALean/ContDynamics/NonlinDASys/Operations/ReachUnion.lean), [`NonlinDASys.WithSteps.reachUnion_outer`](../../../src/CORALean/ContDynamics/NonlinDASys/Theorems/ReachUnionOuter.lean), [`NonlinDASys.WithSteps.reachUnionExact`](../../../src/CORALean/ContDynamics/NonlinDASys/Definitions/ReachUnionExact.lean), [`NonlinDASys.WithSteps.reachYUnion_subset_image`](../../../src/CORALean/ContDynamics/NonlinDASys/Theorems/ReachYUnionSubsetImage.lean) | reduced-model route, not CORA's algorithm: the algebraic variable is eliminated through a supplied `ReducedModel` and the `NonlinearSys` re-linearization run is used; CORA's linearization of the DAE with an algebraic error term is not formalized. The outer theorem is stated against the DAE semantics (every `Trajectory` of `f`, `g`); `y` lies in `h` of the state union times `U` |
| `reach_adaptive` | — | — |  |
| `simulate` | — | — |  |
| `steadyState` | — | — |  |
