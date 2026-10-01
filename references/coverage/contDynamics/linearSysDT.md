# contDynamics/@linearSysDT

CORA methods of `contDynamics/@linearSysDT/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `LinearSysDT`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `computeGO` | — | — |  |
| `confSynth_dyn` | — | — |  |
| `confSynth_gray` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `executeObserver` | — | — |  |
| `falsify` | — | — |  |
| `getPrintSystemInfo` | — | — |  |
| `identify` | — | — |  |
| `isconform_dyn` | — | — |  |
| `linearARX` | — | — |  |
| `linearSys` | — | — |  |
| `linearSysDT` | float | [`LinearSysDT.toLinParam`](../../../src/CORALean/ContDynamics/LinParamSysDT/Theorems/ToLinParam.lean), [`LinearSysDT.reach_eq_toLinParam`](../../../src/CORALean/ContDynamics/LinParamSysDT/Theorems/ReachEqToLinParam.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `outputSet` | float | [`LinearSysDT.output_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/OutputOuter.lean), [`OutputEq.outputSet`](../../../src/CORALean/ContDynamics/OutputEq/Operations/OutputSet.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `post` | float | [`LinearSysDT.reach_one_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOneOuter.lean), [`LinearSysDT.reach`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/Reach.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `reach` | float | [`LinearSysDT.reach`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/Reach.lean), [`LinearSysDT.reachOrders`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachOrders.lean), [`LinearSysDT.reachErrorReduced`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachErrorReduced.lean), [`LinearSysDT.reach_eq_toLinParam`](../../../src/CORALean/ContDynamics/LinParamSysDT/Theorems/ReachEqToLinParam.lean), [`LinearSysDT.reach_one_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOneOuter.lean), [`LinearSysDT.reach_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOuter.lean), [`LinearSysDT.reach_outer_on`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachOuterOn.lean) · float: [`LinearSysDT.reachErrorFloat`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachErrorFloat.lean), [`LinearSysDT.reach_float_subset_reachSet_add_error`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachFloatSubsetReachSetAddError.lean) |  |
| `simulate` | proved | [`LinearSysDT.simulate_mem_reach`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/SimulateMemReach.lean) |  |
| `simulateConstrained` | — | — |  |
