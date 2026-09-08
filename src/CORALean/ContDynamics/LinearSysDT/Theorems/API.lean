import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachExistsOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachForallInner
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachForallInnerZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetExistsPreimage
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetExistsTrajectory
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
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachErrorReducedContainsReachError
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachInnerInner
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachInnerReducedInner
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachInnerReducedSubsetReachInner
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachInnerRepInner
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLe
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLeConZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetBound
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetConvex
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetInnerOfOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetIsCompact
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetSubsetReach
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSubsetReachSetAddError
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSubsetReachSetAddErrorReduced
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateMemReach
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateTrajectory

/-!
# What `LinearSysDT` guarantees

That `reach` contains every trajectory, and what checking a specification on
it then buys. `ReachOneOuter` is its step alone, which a closed loop takes
instead. `ReachSet` is what `reach` encloses, exactly; its theorems bound it
and, convex and compact, let an enclosure be inverted — which is what
`ReachSubsetReachSetAddError` and `ReachInnerInner` do, composing into the one
theorem here with `reachSet` on the *right* of the inclusion, and
`ReachInnerRepInner` is that at a zonotope. The `Reduced` four are the same
with the error reduced at every step: sound because the error is *added* to
the exact set and so may grow, worth it because reducing bounds its size.

The `BackReach` files run the other way: `backReachForall` sits inside
`backReachSetForall` — inner, and only `Zonotope` discharges it — while the `∃`
reading's step is a sum, so `backReachExists` is outer, at `Plus` and `Mtimes`.

`OutputOuter` and `HoldsOfOutput` are those two at an `OutputEq` paired with the
run: what the system emits, not only where it is. `HeldToTrajectory` and
`ReachHeldOuter` are the zero-order-hold case, in closed form.
`SimulateTrajectory` and `SimulateMemReach` sample one run into `reach`, and
`NotHoldsOfSimulate` is the point: a sample falsifies what an enclosure cannot.
`ReachOrderLe` and `ReachBigO` are `reach`'s size, not its content, `reduce` in
the loop keeping it bounded; the `ConZonotope` pair restate both.
-/
