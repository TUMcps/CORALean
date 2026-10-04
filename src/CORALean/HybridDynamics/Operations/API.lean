import CORALean.HybridDynamics.Operations.CalcBasisBox
import CORALean.HybridDynamics.Operations.Jump
import CORALean.HybridDynamics.Operations.JumpIntersection
import CORALean.HybridDynamics.Operations.JumpOfPoint
import CORALean.HybridDynamics.Operations.JumpIntersectionOfPoint
import CORALean.HybridDynamics.Operations.TimeIntervalStep
import CORALean.HybridDynamics.Operations.TimeIntervalStepInv
import CORALean.HybridDynamics.Operations.TimeIntervalStepSplit
import CORALean.HybridDynamics.Operations.TimeIntervalStepFloat
import CORALean.HybridDynamics.Operations.TimeIntervalStepSplitFloat
import CORALean.HybridDynamics.Operations.TimeIntervalStepInvFloat
import CORALean.HybridDynamics.Operations.GuardIntersectFloat
import CORALean.HybridDynamics.Operations.JumpFloat
import CORALean.HybridDynamics.Operations.LocationReachFloat
import CORALean.HybridDynamics.Operations.ReachFloat
import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
import CORALean.HybridDynamics.Operations.NonlinearResetLift
import CORALean.HybridDynamics.Operations.NonlinearResetSynchronize
import CORALean.HybridDynamics.Operations.LinearResetLift
import CORALean.HybridDynamics.Operations.LinearResetSynchronize
import CORALean.HybridDynamics.Operations.TransitionToNonlinearReset
import CORALean.HybridDynamics.Operations.SdcFlow
import CORALean.HybridDynamics.Operations.LocationPotInt
import CORALean.HybridDynamics.Operations.LocationPotOut
import CORALean.HybridDynamics.Operations.GuardIntersectNondetFloat
import CORALean.HybridDynamics.Operations.GuardIntersectPolytopeFloat
import CORALean.HybridDynamics.Operations.TransitionConvGuard
import CORALean.HybridDynamics.Operations.TrajectoryError

/-!
# What a hybrid automaton computes, collected

`Jump` propagates the reset over a set already cut to the guard; `JumpIntersection`
cuts it there itself, at a representation with an `Intersection` instance. The flow
enclosure is `LinearSys`'s, named again here only so that a statement about it
reads its representation off the location; `TimeIntervalStepInv` cuts it to
the invariant the same way, for a representation that has one, and
`TimeIntervalStepSplit` computes its input contribution without asking the
location's input set to hold the origin; `…Float` are the two at float zonotopes.

`JumpOfPoint`/`JumpIntersectionOfPoint` are the same pair at `OfPoint`, the weaker class
the offset actually needs — what lets `ConPolyZono`, having no `OfInterval`
instance, jump at all (#38).

`Jump`, `JumpOfPoint` and both `TimeIntervalStep`s read nothing of the guard or
the invariant, so they leave that representation free. The three that call
`Intersection.intersection` cannot: `Intersection` is homogeneous, so they ask for it in `S` (#39).

At float zonotopes, which have no `Intersection` and no `Real.OfInterval`: the
cuts go through a box, `TimeIntervalStepInvFloat` to the invariant and
`GuardIntersectFloat` to a guard; `JumpFloat` resets; `LocationReachFloat` is a
stay's time-interval sets, and `ReachFloat` the automaton's, CORA's `reach`.
-/
