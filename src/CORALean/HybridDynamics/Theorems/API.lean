import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.HoldsAllOfInvariant
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.HoldsOfRunOn
import CORALean.HybridDynamics.Theorems.InvariantOnOfInvariant
import CORALean.HybridDynamics.Theorems.JumpOuter
import CORALean.HybridDynamics.Theorems.JumpOuterConZonotope
import CORALean.HybridDynamics.Theorems.LinearEmbedding
import CORALean.HybridDynamics.Theorems.ResetImageSubset
import CORALean.HybridDynamics.Theorems.RunExistsRunOn
import CORALean.HybridDynamics.Theorems.RunOnOuter
import CORALean.HybridDynamics.Theorems.RunOnToRun
import CORALean.HybridDynamics.Theorems.RunOuter

/-!
# What a hybrid run guarantees, collected

Read in the order a step is taken. `LinearEmbedding` makes a stay a linear
trajectory and `FlowOuter` encloses it; `JumpOuter` intersects with the guard
and applies the reset, `ResetImageSubset` restates it as a set inclusion, and
`JumpOuterConZonotope` discharges the one hypothesis `JumpOuter` leaves.
`RunOuter` chains the two by induction on the run, and `HoldsOfRun` /
`HoldsAllOfInvariant` turn the result into an answer, one specification or a
list of them.

The bounded-horizon reading: `RunOnToRun`/`RunExistsRunOn` relate `RunOn` to
`Run`, `RunOnOuter` is `RunOuter` at an index, `HoldsOfRunOn` its corollary, and
`InvariantOnOfInvariant` reads an `Invariant` as the constant-family case.
-/
