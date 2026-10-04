import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachForallInnerZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorReducedContainsReachError
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorReducedOrdersSubsetReachErrorOrders
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachHeldOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachInnerInner
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachInnerReducedInner
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachInnerReducedSubsetReachInner
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachInnerRepInner
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachOrdersStepClosedBallOfReduceBoxOrder
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachStepSubsetClosedBall
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachSubsetClosedBall
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachSubsetReachSetAddError
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachSubsetReachSetAddErrorReduced
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ExactUncertainSetEq
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObserveStepOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObserveStripBasedOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.QuadFormLeOfLmi

/-!
# What holds of `LinearSysDT` only at `𝕋 := ℝ`, collected

Each statement here rests on a `Zonotope` operation that is exact only at the exact scalar:
`ReachSubsetReachSetAddError`/`Reduced` and the `Inner` four read `reach` and `reachSet` apart
through `mtimes_exact`/`plus_exact`/`reduce_outer`, which a machine scalar pays into an error box
instead. `ReachInnerRepInner` is `ReachInnerInner` composed with `minkDiffRep_inner`, and
`BackReachForallInnerZonotope` is the backward step at the one representation that can run it,
`mtimes_exact` giving its invertibility hypothesis.

`ReachHeldOuter` is the zero-order-hold run in closed form. The `ClosedBall` three bound `reach`'s
width against `Zonotope.Real`'s own bounds, `StepSubsetClosedBall`/`ReduceBoxAbsBoundLe` among them.
-/
