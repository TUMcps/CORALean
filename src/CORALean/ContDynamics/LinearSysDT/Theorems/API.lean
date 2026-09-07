import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachForallInner
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachForallInnerZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetForallTrajectory
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
`ReachOneOuter` is its step alone, which a closed loop takes instead. `ReachSet`
is what `reach` encloses, exactly; the three theorems named for it and
`HoldsOfSeparating` check a specification by support bound, no set built at all.

The `BackReach` three run the other way: `backReachSetForall` holds every run
into the target, and `backReachForall` sits *inside* it — inner, a backward set
being a guarantee — at the one representation `...Zonotope` names.

`OutputOuter` and `HoldsOfOutput` are those two again at an `OutputEq` paired
with the run: a requirement about what the system emits, not only where it is.
`HeldToTrajectory` and `ReachHeldOuter` are the zero-order-hold case: a held run
is a restriction of `Trajectory`, and `reachHeld` encloses it in closed form.

`SimulateTrajectory` and `SimulateMemReach` sample one run into `reach`, and
`NotHoldsOfSimulate` is the point: a sample falsifies what an enclosure cannot.

`ReachOrderLe` and `ReachBigO` are `reach`'s size, not its content: `reduce` in
the loop keeps it bounded as `k` grows, and the `O(1)` form is that as growth.
The `ConZonotope` pair restate both: never `Zonotope`, only `reduce`.
-/
