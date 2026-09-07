import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.FlowOuterInputSolution
import CORALean.HybridDynamics.Theorems.HoldsAllOfInvariant
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.HoldsOfRunOn
import CORALean.HybridDynamics.Theorems.InvariantOfEnclosure
import CORALean.HybridDynamics.Theorems.InvariantOnOfInvariant
import CORALean.HybridDynamics.Theorems.JumpAndOuter
import CORALean.HybridDynamics.Theorems.JumpOuter
import CORALean.HybridDynamics.Theorems.JumpOuterConZonotope
import CORALean.HybridDynamics.Theorems.JumpOfPointOuter
import CORALean.HybridDynamics.Theorems.JumpAndOfPointOuter
import CORALean.HybridDynamics.Theorems.LinearEmbedding
import CORALean.HybridDynamics.Theorems.ResetImageSubset
import CORALean.HybridDynamics.Theorems.RunExistsRunOn
import CORALean.HybridDynamics.Theorems.RunOnOuter
import CORALean.HybridDynamics.Theorems.RunOnToRun
import CORALean.HybridDynamics.Theorems.RunOuter
import CORALean.HybridDynamics.Theorems.TimeIntervalInvOuter

/-!
# What a hybrid run guarantees, collected

Read in the order a step is taken. `LinearEmbedding` makes a stay a linear
trajectory, `FlowOuter` encloses it and `TimeIntervalInvOuter` cuts that to the
invariant; `JumpOuter` intersects with the guard and applies the reset,
`ResetImageSubset` restates it as a set inclusion, `JumpOuterConZonotope`
discharges the one hypothesis `JumpOuter` leaves without an `And` instance,
and `JumpAndOuter` is the case where one discharges it. `RunOuter` chains the
two by induction on the run, and `HoldsOfRun`/`HoldsAllOfInvariant` turn the
result into an answer, one specification or a list of them.

The bounded-horizon reading: `RunOnToRun`/`RunExistsRunOn` relate `RunOn` to
`Run`, `RunOnOuter` is `RunOuter` at an index, `HoldsOfRunOn` its corollary, and
`InvariantOnOfInvariant` reads an `Invariant` as the constant-family case.

`FlowOuterInputSolution` computes `FlowOuter`'s input contribution instead of
naming it, and `InvariantOfEnclosure` is what that buys: a criterion on `R`
built from it and `JumpAndOuter` that proves `HybridAutomaton.Invariant R`.

`JumpOfPointOuter`/`JumpAndOfPointOuter` read the same two guarantees at
`OfPoint`, which `ConPolyZono` has and `OfInterval` it does not (#38).
-/
