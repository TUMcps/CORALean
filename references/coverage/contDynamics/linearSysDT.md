# contDynamics/@linearSysDT

CORA methods of `contDynamics/@linearSysDT/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `LinearSysDT`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `computeGO` | proved | [`LinearSysDT.computeGO`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ComputeGO.lean), [`LinearSysDT.computeGO_state`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ComputeGOState.lean), [`LinearSysDT.computeGO_output`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ComputeGOOutput.lean) | exact: for every run, `x(k+1) = A{k} x(0) + ∑_j B{k,j} u(j)` and `y(k) = C{k} x(0) + ∑_j D{k,j} u(j)`. Real layer (`noncomputable`: real matrix powers), not float. Time-invariant branch only, with the input in state coordinates (`B = 1`) and the output equation `OutputEq`; not kept: the time-varying branch, `F`, `E` (linearization error) and the reference signals |
| `confSynth_dyn` | out-of-scope | n/a — solver-dependent | result determined by `linprog`/`quadprog` |
| `confSynth_gray` | out-of-scope | n/a — solver-dependent | result determined by `fmincon` |
| `display` | out-of-scope | n/a — plotting/display |  |
| `executeObserver` | proved | [`LinearSysDT.observeStripBased`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStripBased.lean), [`LinearSysDT.observeStripBased_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveStripBasedOuter.lean) | the strip-based estimators `FRad-A`, `FRad-B`, `PRad-A` to `PRad-D` and `VolMin-A` only, through `observe_stripBased`; the others are not covered |
| `falsify` | out-of-scope | n/a — solver-dependent | optimisation and wall-clock search for a falsifying trajectory |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `identify` | — | — |  |
| `isconform_dyn` | — | — |  |
| `linearARX` | — | — |  |
| `linearSys` | — | — |  |
| `linearSysDT` | float | [`LinearSysDT.toLinParam`](../../../src/CORALean/ContDynamics/LinParamSysDT/Theorems/ToLinParam.lean), [`LinearSysDT.reach_eq_toLinParam`](../../../src/CORALean/ContDynamics/LinParamSysDT/Theorems/ReachEqToLinParam.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `outputSet` | float | [`LinearSysDT.output_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/OutputOuter.lean), [`OutputEq.outputSet`](../../../src/CORALean/ContDynamics/OutputEq/Operations/OutputSet.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `post` | float | [`LinearSysDT.reach_one_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOneOuter.lean), [`LinearSysDT.reach`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/Reach.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `reach` | float | [`LinearSysDT.reach`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/Reach.lean), [`LinearSysDT.reachOrders`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachOrders.lean), [`LinearSysDT.reachErrorReduced`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachErrorReduced.lean), [`LinearSysDT.reach_eq_toLinParam`](../../../src/CORALean/ContDynamics/LinParamSysDT/Theorems/ReachEqToLinParam.lean), [`LinearSysDT.reach_one_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOneOuter.lean), [`LinearSysDT.reach_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOuter.lean), [`LinearSysDT.reach_outer_on`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOuterOn.lean) · float: [`LinearSysDT.reachErrorFloat`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachErrorFloat.lean), [`LinearSysDT.reach_float_subset_reachSet_add_error`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachFloatSubsetReachSetAddError.lean) |  |
| `simulate` | float | [`LinearSysDT.simulate_mem_reach`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/SimulateMemReach.lean) · float: [`LinearSysDT.simulateBox`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/SimulateBoxFloat.lean), [`LinearSysDT.simulate_mem_simulateBox`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/SimulateMemSimulateBoxFloat.lean) | R-SIM — outer: the real run lies in the float boxes of the step on `Interval.point` start and inputs, directed rounding
| `simulateConstrained` | out-of-scope | n/a — random/sampling | draws `randPoint` of the noise sets and solves a `linprog` per step |
