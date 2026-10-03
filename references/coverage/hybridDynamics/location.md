# hybridDynamics/@location

CORA methods of `hybridDynamics/@location/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Location`, `Transition`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `adaptOptions` | — | — |  |
| `calcBasis` | — | — |  |
| `checkFlow` | — | — |  |
| `derivatives` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `eq` | out-of-scope | n/a — matlab-runtime |  |
| `eventFcn` | out-of-scope | n/a — matlab-runtime | ODE event callback |
| `guardIntersect` | float | [`Transition.jumpIntersection`](../../../src/CORALean/HybridDynamics/Operations/JumpIntersection.lean), [`Transition.jumpIntersection_outer`](../../../src/CORALean/HybridDynamics/Theorems/JumpIntersectionOuter.lean) · float: [`Location.guardIntersectFloat`](../../../src/CORALean/HybridDynamics/Operations/GuardIntersectFloat.lean), [`Location.guardIntersectFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/GuardIntersectFloatOuter.lean) | float side is CORA's `'box'` method: each time-interval set boxed, cut to the invariant and the guard by `HPolytope.contractBox` (one pass of interval constraint propagation per row), the cuts not certified empty joined by their box hull |
| `guardIntersect_conZonotope` | float | [`Transition.jump_outer_conZonotope`](../../../src/CORALean/HybridDynamics/Theorems/JumpOuterConZonotope.lean) · float: [`ConZonotope.intersection`](../../../src/CORALean/ContSet/ConZonotope/Float/Operations/Intersection.lean), [`Transition.jumpFloat_outer_conZonotope`](../../../src/CORALean/HybridDynamics/Theorems/JumpFloatOuterConZonotope.lean) | route a — guard cut by the float `ConZonotope.intersection`, reset by float `mtimes` and `plus` of the zero-width box at `w`; outer where the real theorem is lossless at the cut |
| `guardIntersect_hyperplaneMap` | — | — |  |
| `guardIntersect_levelSet` | — | — |  |
| `guardIntersect_nondetGuard` | — | — |  |
| `guardIntersect_pancake` | — | — |  |
| `guardIntersect_polytope` | — | — |  |
| `guardIntersect_zonoGirard` | — | — |  |
| `instantReset` | float | [`Transition.reset`](../../../src/CORALean/HybridDynamics/Definitions/Transition.lean), [`Transition.reset_image_subset`](../../../src/CORALean/HybridDynamics/Theorems/ResetImageSubset.lean) · float: [`Transition.jumpFloat`](../../../src/CORALean/HybridDynamics/Operations/JumpFloat.lean), [`Transition.jumpFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/JumpFloatOuter.lean) |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `location` | float | [`Location`](../../../src/CORALean/HybridDynamics/Definitions/Location.lean), [`Location.Trajectory.timeInterval_outer`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuter.lean) · float: [`Location.timeIntervalStepFloat`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepFloat.lean), [`Location.Trajectory.timeIntervalFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuterFloat.lean) | route a — the float twin of the linked time-interval enclosure; the structure, and the theorem that every state of a stay lies in the time-interval enclosure |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `potInt` | — | — |  |
| `potOut` | — | — |  |
| `reach` | float | [`Location.timeIntervalStep`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStep.lean), [`Location.timeIntervalStepInv`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepInv.lean), [`Location.timeIntervalStepSplit`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepSplit.lean), [`Location.Trajectory.timeInterval_outer`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuter.lean), [`Location.Trajectory.timeIntervalInv_outer`](../../../src/CORALean/HybridDynamics/Theorems/TimeIntervalInvOuter.lean), [`Location.Trajectory.timeInterval_outer_split`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuterSplit.lean) · float: [`Location.reachFloat`](../../../src/CORALean/HybridDynamics/Operations/LocationReachFloat.lean), [`Location.Trajectory.reachFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/LocationReachFloatOuter.lean), [`Location.timeIntervalStepFloat`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepFloat.lean), [`Location.Trajectory.timeIntervalFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuterFloat.lean), [`Location.timeIntervalStepSplitFloat`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepSplitFloat.lean), [`Location.Trajectory.timeIntervalSplitFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/FlowOuterSplitFloat.lean), [`Location.timeIntervalStepInvFloat`](../../../src/CORALean/HybridDynamics/Operations/TimeIntervalStepInvFloat.lean), [`Location.Trajectory.timeIntervalInvFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/TimeIntervalInvFloatOuter.lean) | the float cut to the invariant goes through a box (`Zonotope.interval`, then `HPolytope.contractBox` by the invariant's rows), coarser than the zonotope where no row cuts; `Location.reachFloat` is a stay of up to `tFinal` by `LinearSys.reachFloatInput` |
| `simulate` | — | — |  |
