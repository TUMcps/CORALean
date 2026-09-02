import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.JumpOuter
import CORALean.HybridDynamics.Theorems.JumpOuterConZonotope
import CORALean.HybridDynamics.Theorems.LinearEmbedding
import CORALean.HybridDynamics.Theorems.RunOuter

/-!
# What a hybrid run guarantees, collected

Read in the order a step is taken. `LinearEmbedding` makes a stay a linear
trajectory and `FlowOuter` encloses it; `JumpOuter` intersects with the guard
and applies the reset, and `JumpOuterConZonotope` discharges the one hypothesis
it leaves. `RunOuter` chains the two by induction on the run, and `HoldsOfRun`
turns the result into an answer.
-/
