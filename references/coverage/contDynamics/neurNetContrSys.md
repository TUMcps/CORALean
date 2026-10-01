# contDynamics/@neurNetContrSys

CORA methods of `contDynamics/@neurNetContrSys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NeurNetContrSys`, `NeurNetContrSysDT`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `neurNetContrSys` | — | — |  |
| `reach` | float | [`NeurNetContrSys.reach`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Operations/Reach.lean), [`NeurNetContrSysDT.reach`](../../../src/CORALean/ContDynamics/NeurNetContrSysDT/Operations/Reach.lean), [`NeurNetContrSys.reachSet`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Definitions/ReachSet.lean), [`NeurNetContrSys.reach_outer`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Theorems/ReachOuter.lean), [`NeurNetContrSysDT.reach_outer`](../../../src/CORALean/ContDynamics/NeurNetContrSysDT/Theorems/ReachOuter.lean), [`NeurNetContrSys.Trajectory.reachSet_outer`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Theorems/ReachSetOuter.lean), [`NeurNetContrSys.reachSet_subset_reach`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Theorems/ReachSetSubsetReach.lean) · float: [`NeurNetContrSys.reachFloat`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Operations/ReachFloat.lean), [`NeurNetContrSys.reachFloat_outer`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Theorems/ReachFloatOuter.lean) | the float run takes the Taylor order as given and asks it admissible; the `Reach` instance's union over it (`reachUnion`) is pending #1 |
| `simulate` | proved | [`NeurNetContrSysDT.simulate_mem_reach`](../../../src/CORALean/ContDynamics/NeurNetContrSysDT/Theorems/SimulateMemReach.lean) |  |
| `verify` | proved | [`NeurNetContrSys.reach`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Operations/Reach.lean), [`NeurNetContrSys.holds_of_check`](../../../src/CORALean/ContDynamics/NeurNetContrSys/Theorems/HoldsOfCheck.lean) | the `VERIFIED` verdict only: a spec checked on the computed reach set holds; no simulation-based `VIOLATED` branch for the continuous plant |
