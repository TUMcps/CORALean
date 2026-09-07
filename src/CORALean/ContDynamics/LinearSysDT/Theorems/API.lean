import CORALean.ContDynamics.LinearSysDT.Theorems.HeldToTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfSeparating
import CORALean.ContDynamics.LinearSysDT.Theorems.NotHoldsOfSimulate
import CORALean.ContDynamics.LinearSysDT.Theorems.OutputOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachBigO
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachBigOConZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachHeldOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLe
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLeConZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetBound
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetSubsetReach
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateMemReach
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateTrajectory

/-!
# What `LinearSysDT` guarantees

That `reach` contains every trajectory, which is the one thing there is to
prove about a discrete run, and what checking a specification on it then buys.
`ReachOneOuter` is its step in isolation, which is what a run whose input set
changes each step — a closed loop — takes instead. `ReachSet` is what `reach`
encloses, exactly; the three theorems named for it and `HoldsOfSeparating`
check a specification by support bound, with no set built at all.

`OutputOuter` and `HoldsOfOutput` are those two again at an `OutputEq` paired
with the run: a requirement about what the system emits, not only where it is.

`HeldToTrajectory` and `ReachHeldOuter` are the zero-order-hold case: a held run
is a restriction of `Trajectory`, and `reachHeld` encloses it exactly, in closed
form rather than through `reach`'s per-step jitter.

`SimulateTrajectory` and `SimulateMemReach` are `simulate` sampling one run and
landing inside `reach`; `NotHoldsOfSimulate` is why that is worth having — one
sampled run can falsify a specification an enclosure can only fail to prove.

`ReachOrderLe` and `ReachBigO` are the size, not the content, of `reach`:
`reduce` in the loop keeps it bounded as `k` grows, and the `O(1)` form is that
as growth. The `ConZonotope` pair restate both: never `Zonotope`, only `reduce`.
-/
