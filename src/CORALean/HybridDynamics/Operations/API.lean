import CORALean.HybridDynamics.Operations.CalcBasisBox
import CORALean.HybridDynamics.Operations.HitHessianMatZono
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
import CORALean.HybridDynamics.Operations.LocationReachFloatChecked
import CORALean.HybridDynamics.Operations.ReachFloat
import CORALean.HybridDynamics.Operations.ReachFloatChecked
import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
import CORALean.HybridDynamics.Operations.NonlinearResetEvaluateFloat
import CORALean.HybridDynamics.Operations.NonlinearResetLift
import CORALean.HybridDynamics.Operations.NonlinearResetLiftFloat
import CORALean.HybridDynamics.Operations.NonlinearResetSynchronize
import CORALean.HybridDynamics.Operations.NonlinearResetSynchronizeFloat
import CORALean.HybridDynamics.Operations.LinearResetLift
import CORALean.HybridDynamics.Operations.LinearResetSynchronize
import CORALean.HybridDynamics.Operations.LinearResetSynchronizeFloat
import CORALean.HybridDynamics.Operations.TransitionToNonlinearReset
import CORALean.HybridDynamics.Operations.TransitionToNonlinearResetFloat
import CORALean.HybridDynamics.Operations.SdcFlow
import CORALean.HybridDynamics.Operations.LocationPotInt
import CORALean.HybridDynamics.Operations.LocationPotOut
import CORALean.HybridDynamics.Operations.GuardIntersectNondetFloat
import CORALean.HybridDynamics.Operations.GuardIntersectPolytopeFloat
import CORALean.HybridDynamics.Operations.GuardIntersectZonoGirardFloat
import CORALean.HybridDynamics.Operations.ZonoGirardUpperFloat
import CORALean.HybridDynamics.Operations.CheckFlowFloat
import CORALean.HybridDynamics.Operations.TransitionConvGuard
import CORALean.HybridDynamics.Operations.TrajectoryError
import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope
import CORALean.HybridDynamics.Operations.TransitionSynchronize
import CORALean.HybridDynamics.Operations.TransitionSynchronizeGuard
import CORALean.HybridDynamics.Operations.TransitionSynchronizeTarget
import CORALean.HybridDynamics.Operations.TransitionSynchronizeTargetCORA
import CORALean.HybridDynamics.Operations.IdentGuard
import CORALean.HybridDynamics.Operations.SplitTreeRegions
import CORALean.HybridDynamics.Operations.Scatter
import CORALean.HybridDynamics.Operations.LinearResetResolveUpdate
import CORALean.HybridDynamics.Operations.LinearResetResolve
import CORALean.HybridDynamics.Operations.NonlinearResetResolve
import CORALean.HybridDynamics.Operations.NonlinearResetResolveFloat
import CORALean.HybridDynamics.Operations.NonlinearResetGlobalColumns
import CORALean.HybridDynamics.Operations.NonlinearResetGlobalRank
import CORALean.HybridDynamics.Operations.NonlinearResetResolveCORA
import CORALean.HybridDynamics.Operations.ReachGuard
import CORALean.HybridDynamics.Operations.GuardIntersectLevelSet
import CORALean.HybridDynamics.Operations.GuardTransitionLevelSet
import CORALean.HybridDynamics.Operations.AbstractionError
import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMap
import CORALean.HybridDynamics.Operations.AbstractionErrorFloat
import CORALean.HybridDynamics.Operations.HitPointFloat
import CORALean.HybridDynamics.Operations.HitJacobianFloat
import CORALean.HybridDynamics.Operations.HitHessianMatZonoFloat
import CORALean.HybridDynamics.Operations.SdcInputFloat
import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMapFloat

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
stay's time-interval sets, and `ReachFloat` the automaton's, CORA's `reach`. `ReachGuard` is a
stay's sets up to leaving the invariant and their enclosure at a guard, its operators passed in.
-/
