# contDynamics/@linearARX

CORA methods of `contDynamics/@linearARX/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `LinearARX`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `computeGO` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `identify` | — | — |  |
| `linearARX` | float | [`LinearARX`](../../../src/CORALean/ContDynamics/LinearARX/LinearARX.lean), [`LinearARX.toLinearSysDT_trajectory`](../../../src/CORALean/ContDynamics/LinearARX/Theorems/ToLinearSysDTTrajectory.lean) | route b — the structure is generic over `Scalar 𝕋` and computable, and the theorem is stated for it; the structure, and the theorem that every ARX run is a run of its `LinearSysDT` conversion |
| `reach` | float | [`LinearARX.reach_outer`](../../../src/CORALean/ContDynamics/LinearARX/Theorems/ReachOuter.lean), [`LinearARX.toLinearSysDT`](../../../src/CORALean/ContDynamics/LinearARX/Operations/ToLinearSysDT.lean) | route b — generic over `Scalar 𝕋` with `ExactScalar 𝕋` (float instance), computable (`toLinearSysDT` only places `0` and `1`) |
| `simulate` | proved | [`LinearARX.simulate`](../../../src/CORALean/ContDynamics/LinearARX/Operations/Simulate.lean), [`LinearARX.simulate_trajectory`](../../../src/CORALean/ContDynamics/LinearARX/Theorems/SimulateTrajectory.lean), [`LinearARX.simulate_mem_reach`](../../../src/CORALean/ContDynamics/LinearARX/Theorems/SimulateMemReach.lean) | normal parametrization only (CORA's `tvp` branch is not modelled); the simulated outputs are a `Trajectory`, and each window lies in the reach set |
