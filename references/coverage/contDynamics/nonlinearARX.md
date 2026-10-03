# contDynamics/@nonlinearARX

CORA methods of `contDynamics/@nonlinearARX/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinearARX`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `computeGO` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `identify` | out-of-scope | n/a — solver-dependent | result determined by genetic programming (`rungp`) |
| `nonlinearARX` | proved | [`NonlinearARX`](../../../src/CORALean/ContDynamics/NonlinearARX/NonlinearARX.lean), [`NonlinearARX.toNonlinearSysDT_trajectory`](../../../src/CORALean/ContDynamics/NonlinearARX/Theorems/ToNonlinearSysDTTrajectory.lean) | the structure (`f` over `ℝ`, order `p`, dimensions) with its ARX-form `Trajectory`, and the theorem that every ARX run is a run of its `NonlinearSysDT` conversion; the cached Jacobian, Hessian and tensor are the converted system's `LinStep` |
| `nonlinearSysDT` | proved | [`NonlinearARX.toNonlinearSysDT`](../../../src/CORALean/ContDynamics/NonlinearARX/Operations/ToNonlinearSysDT.lean), [`NonlinearARX.toNonlinearSysDT_step`](../../../src/CORALean/ContDynamics/NonlinearARX/Theorems/ToNonlinearSysDTStep.lean) | state of `dim_y · p` stacking the last outputs, input of `dim_u (p+1)` stacking the inputs, as CORA; `f_ARX` reads its arguments newest first, so the blocks are reversed on the way in |
| `reach` | float | [`NonlinearARX.reach_outer`](../../../src/CORALean/ContDynamics/NonlinearARX/Theorems/ReachOuter.lean), [`NonlinearARX.output_outer`](../../../src/CORALean/ContDynamics/NonlinearARX/Theorems/OutputOuter.lean), [`NonlinearSysDT.reach`](../../../src/CORALean/ContDynamics/NonlinearSysDT/Operations/Reach.lean), [`NonlinearARX.outputSel`](../../../src/CORALean/ContDynamics/NonlinearARX/Operations/OutputSel.lean) | route b — generic over the scalar `𝕋` and the set representation, computable (outer): through `NonlinearSysDT.reach_outer` on the conversion, the input set and the linearizations supplied; ARX-form reach itself is not stated, and no input dependency is lost, unlike `LinearARX` |
| `simulate` | proved | [`NonlinearARX.simulate`](../../../src/CORALean/ContDynamics/NonlinearARX/Operations/Simulate.lean), [`NonlinearARX.simulate_trajectory`](../../../src/CORALean/ContDynamics/NonlinearARX/Theorems/SimulateTrajectory.lean), [`NonlinearARX.simulate_mem_reach`](../../../src/CORALean/ContDynamics/NonlinearARX/Theorems/SimulateMemReach.lean) | the simulated outputs are a `Trajectory`, and each window lies in the reach set |
