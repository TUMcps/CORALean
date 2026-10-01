# hybridDynamics/@location

CORA methods of `hybridDynamics/@location/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Location`, `Transition`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `adaptOptions` | — | — |  |
| `calcBasis` | — | — |  |
| `checkFlow` | — | — |  |
| `derivatives` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `eq` | — | — |  |
| `eventFcn` | — | — |  |
| `guardIntersect` | proved | [`Transition.jumpIntersection`](../../../src/CORALean/HybridDynamics/Operations/JumpIntersection.lean), [`Transition.jumpIntersection_outer`](../../../src/CORALean/HybridDynamics/Theorems/JumpIntersectionOuter.lean) |  |
| `guardIntersect_conZonotope` | proved | [`Transition.jump_outer_conZonotope`](../../../src/CORALean/HybridDynamics/Theorems/JumpOuterConZonotope.lean) |  |
| `guardIntersect_hyperplaneMap` | — | — |  |
| `guardIntersect_levelSet` | — | — |  |
| `guardIntersect_nondetGuard` | — | — |  |
| `guardIntersect_pancake` | — | — |  |
| `guardIntersect_polytope` | — | — |  |
| `guardIntersect_zonoGirard` | — | — |  |
| `instantReset` | proved | [`Transition.reset`](../../../src/CORALean/HybridDynamics/Definitions/Transition.lean), [`Transition.reset_image_subset`](../../../src/CORALean/HybridDynamics/Theorems/ResetImageSubset.lean) |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `location` | — | — |  |
| `ne` | — | — |  |
| `potInt` | — | — |  |
| `potOut` | — | — |  |
| `reach` | proved | [`Location.timeIntervalStep`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStep.lean), [`Location.timeIntervalStepInv`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepInv.lean), [`Location.timeIntervalStepSplit`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepSplit.lean), [`Location.Trajectory.timeInterval_outer`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuter.lean), [`Location.Trajectory.timeIntervalInv_outer`](../../../src/CORALean/HybridDynamics/Theorems/TimeIntervalInvOuter.lean), [`Location.Trajectory.timeInterval_outer_split`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuterSplit.lean) | a stay runs in floats as `Location.timeIntervalStepFloat` and `timeIntervalStepSplitFloat` (`Location.Trajectory.timeIntervalFloat_outer`, `timeIntervalSplitFloat_outer`); `timeIntervalStepInv`, the cut to the invariant, is pending #1, so the row stays `proved` |
| `simulate` | — | — |  |
