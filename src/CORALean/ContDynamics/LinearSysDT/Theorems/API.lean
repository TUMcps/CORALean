import CORALean.ContDynamics.LinearSysDT.Theorems.HeldToTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.LinearSysDT.Theorems.OutputOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachHeldOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn

/-!
# What `LinearSysDT` guarantees

That `reach` contains every trajectory, which is the one thing there is to
prove about a discrete run, and what checking a specification on it then buys.
`ReachOneOuter` is its step in isolation, which is what a run whose input set
changes each step — a closed loop — takes instead.

`OutputOuter` and `HoldsOfOutput` are those two again at an `OutputEq` paired
with the run, so a requirement can be written about what the system emits and
not only about where it is.

`HeldToTrajectory` and `ReachHeldOuter` are the zero-order-hold case: a held run
is a restriction of `Trajectory`, and `reachHeld` encloses it exactly, in closed
form rather than through `reach`'s per-step jitter.
-/
