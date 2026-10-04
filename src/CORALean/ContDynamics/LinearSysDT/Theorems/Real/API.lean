import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachForallInnerZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachSetRobustSucc
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachAlignedInner
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachAlignedOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachAlignedControl
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachAlignedFeedback
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
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObserveIntervalOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.QuadFormLeOfLmi
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntersectDescriptorOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObserveDescriptorOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.DescriptorObserverDecay
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObservePropagationOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObserveIntervalCoraCounterexample
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.LuenbergerErrorMemReachErrorSet
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateErrorEqHull
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorSetSuccSubset
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeOfBounds
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalObserverOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeIntervalObserver
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalObserverTransformedOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeIntervalObserverTransformed
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.DissipationOfHinfLmi
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.HinfOfLmi
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ErrorBoundOfHinfLmi
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ErrorBoundOfHinfLmiCounterexample
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntersectDescriptorHdOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.RadiusLmiInfeasible
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.RadiusLeOfContraction
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.PeakDisturbanceCounterexample
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.PeakDisturbanceLe
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.LpvLmiOfVertices
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.LpvLmiOfVerticesCounterexample
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObserveDescriptorLPVOuter

/-!
# What holds of `LinearSysDT` only at `𝕋 := ℝ`, collected

Each statement here rests on a `Zonotope` operation that is exact only at the exact scalar:
`ReachSubsetReachSetAddError`/`Reduced` and the `Inner` four read `reach` and `reachSet` apart
through `mtimes_exact`/`plus_exact`/`reduce_outer`, which a machine scalar pays into an error box
instead. `ReachInnerRepInner` is `ReachInnerInner` composed with `minkDiffRep_inner`, and
`BackReachForallInnerZonotope` is the backward step at the one representation that can run it,
`mtimes_exact` giving its invertibility hypothesis. `BackReachAligned*` is Yang and Ozay's
robust backward recursion at aligned zonotopes, inside and around `backReachSetRobust`, whose
step `BackReachSetRobustSucc` reads as a difference, a sum and a preimage.

`ReachHeldOuter` is the zero-order-hold run in closed form. The `ClosedBall` three bound `reach`'s
width against `Zonotope.Real`'s own bounds, `StepSubsetClosedBall`/`ReduceBoxAbsBoundLe` among them.
-/
