import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachExistsOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachForallInner
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetExistsPreimage
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetExistsTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetForallTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.HeldToTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfCheck
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfSeparating
import CORALean.ContDynamics.LinearSysDT.Theorems.NotHoldsOfSimulate
import CORALean.ContDynamics.LinearSysDT.Theorems.OutputOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachBigO
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachBigOConZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachFloatSubsetReachSetAddError
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachFloatZeroMemError
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachInnerFloatInner
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLe
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLeConZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrdersConstEqReach
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrdersOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetBound
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetConvex
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetInnerOfOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetIsCompact
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetSubsetReach
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetWitness
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.API
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateMemReach
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateTrajectory

/-!
# What `LinearSysDT` guarantees

That `reach` contains every trajectory, and what checking a specification on
it then buys. `ReachOneOuter` is its step alone, which a closed loop takes
instead. `ReachSet` is what `reach` encloses, exactly; its theorems bound it
and, convex and compact, let an enclosure be inverted — which is what
`ReachSubsetReachSetAddError` and `ReachInnerInner` do, with `reachSet` on the
*right*, and `ReachInnerRepInner` is that at a zonotope. The `Reduced` four are
the same with the error reduced at every step, sound because it is *added* to
the exact set. `BackReachForall` sits inside `BackReachSetForall`, inner and
only at `Zonotope`; `BackReachExists` is outer instead, at `Plus, Mtimes`.

`OutputOuter` and `HoldsOfOutput` pair an `OutputEq` with the run.
`HeldToTrajectory` and `ReachHeldOuter` are the zero-order-hold case, closed form.
`SimulateTrajectory` and `SimulateMemReach` sample one run into `reach`;
`NotHoldsOfSimulate` is the point, falsifying what an enclosure cannot.
`ReachOrderLe` and `ReachBigO` are `reach`'s size, `reduce` keeping it bounded; the
`ConZonotope` pair restate both, and the float three restate `ReachSubsetReachSetAddError`
against three bounds, `ReachInnerFloatInner` composing it as `ReachInnerInner` does.
`ReachOrdersOuter` and `ReachOrdersConstEqReach` carry `reach_outer` to a
per-step sequence, recovering `reach` at a constant one; `Real/` holds what
needs ℝ, the reduced-error transfer and the `ClosedBall` bounds among them.
-/
