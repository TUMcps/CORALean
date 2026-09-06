import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.HoldsAllOfInvariant
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.JumpOuter
import CORALean.HybridDynamics.Theorems.JumpOuterConZonotope
import CORALean.HybridDynamics.Theorems.LinearEmbedding
import CORALean.HybridDynamics.Theorems.ResetImageSubset
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
-/
