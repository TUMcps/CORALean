module

public import CORALean.HybridDynamics.Operations.CalcBasisBox
public import CORALean.HybridDynamics.Operations.HitHessianMatZono
public import CORALean.HybridDynamics.Operations.Jump
public import CORALean.HybridDynamics.Operations.JumpIntersection
public import CORALean.HybridDynamics.Operations.JumpIntersectionOfPoint
public import CORALean.HybridDynamics.Operations.InputSet
public import CORALean.HybridDynamics.Operations.InputSetFloat
public import CORALean.HybridDynamics.Operations.TimeInterval
public import CORALean.HybridDynamics.Operations.TimeIntervalInv
public import CORALean.HybridDynamics.Operations.TimeIntervalSplit
public import CORALean.HybridDynamics.Operations.TimeIntervalFloat
public import CORALean.HybridDynamics.Operations.TimeIntervalSplitFloat
public import CORALean.HybridDynamics.Operations.TimeIntervalInvFloat
public import CORALean.HybridDynamics.Operations.GuardIntersectFloat
public import CORALean.HybridDynamics.Operations.JumpFloat
public import CORALean.HybridDynamics.Operations.LocationReachFloat
public import CORALean.HybridDynamics.Operations.LocationReachFloatChecked
public import CORALean.HybridDynamics.Operations.ReachFloat
public import CORALean.HybridDynamics.Operations.ReachFloatChecked
public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluateFloat
public import CORALean.HybridDynamics.Operations.NonlinearResetLift
public import CORALean.HybridDynamics.Operations.NonlinearResetLiftFloat
public import CORALean.HybridDynamics.Operations.NonlinearResetSynchronize
public import CORALean.HybridDynamics.Operations.NonlinearResetSynchronizeFloat
public import CORALean.HybridDynamics.Operations.LinearResetLift
public import CORALean.HybridDynamics.Operations.LinearResetSynchronize
public import CORALean.HybridDynamics.Operations.LinearResetSynchronizeFloat
public import CORALean.HybridDynamics.Operations.LinearResetResolveFloat
public import CORALean.HybridDynamics.Operations.Basic
public import CORALean.HybridDynamics.Operations.TransitionToNonlinearResetFloat
public import CORALean.HybridDynamics.Operations.SdcFlow
public import CORALean.HybridDynamics.Operations.LocationPotInt
public import CORALean.HybridDynamics.Operations.LocationPotOut
public import CORALean.HybridDynamics.Operations.GuardIntersectNondetFloat
public import CORALean.HybridDynamics.Operations.GuardIntersectPolytopeFloat
public import CORALean.HybridDynamics.Operations.GuardIntersectZonoGirardFloat
public import CORALean.HybridDynamics.Operations.ZonoGirardUpperFloat
public import CORALean.HybridDynamics.Operations.CheckFlowFloat
public import CORALean.HybridDynamics.Operations.TransitionConvGuard
public import CORALean.HybridDynamics.Operations.TrajectoryError
public import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope
public import CORALean.HybridDynamics.Operations.TransitionSynchronize
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeGuard
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTarget
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTargetCORA
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeFloat
public import CORALean.HybridDynamics.Operations.IdentGuard
public import CORALean.HybridDynamics.Operations.IdentPolytope
public import CORALean.HybridDynamics.Operations.SplitTreeRegions
public import CORALean.HybridDynamics.Operations.LinearResetResolveUpdate
public import CORALean.HybridDynamics.Operations.LinearResetResolve
public import CORALean.HybridDynamics.Operations.NonlinearResetResolve
public import CORALean.HybridDynamics.Operations.NonlinearResetResolveFloat
public import CORALean.HybridDynamics.Operations.NonlinearResetGlobalRank
public import CORALean.HybridDynamics.Operations.NonlinearResetResolveCORA
public import CORALean.HybridDynamics.Operations.NonlinearResetSynchronizeResolveCORA
public import CORALean.HybridDynamics.Operations.ReachGuard
public import CORALean.HybridDynamics.Operations.GuardIntersectLevelSet
public import CORALean.HybridDynamics.Operations.GuardTransitionLevelSet
public import CORALean.HybridDynamics.Operations.AbstractionError
public import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMap
public import CORALean.HybridDynamics.Operations.GuardIntersectPancake
public import CORALean.HybridDynamics.Operations.AbstractionErrorFloat
public import CORALean.HybridDynamics.Operations.HitHessianMatZonoFloat
public import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMapFloat
public import CORALean.HybridDynamics.Operations.TrajectoryErrorFloat
public import CORALean.HybridDynamics.Operations.MatlabLinspace
public import CORALean.HybridDynamics.Operations.SimulateRandomTimes
public import CORALean.HybridDynamics.Operations.NonlinearResetSecondOrderBound

/-!
# What a hybrid automaton computes, collected

`InputSet` (`InputSetFloat`) is the combined input `B U ⊕ c ⊕ E W` the flow enclosures read.
`Jump` propagates the reset over a set already cut to the guard; `JumpIntersection` cuts it
there itself, at a representation with an `Intersection` instance. The flow
enclosure is `LinearSys`'s, named again so that a statement about it reads its representation off
the location; `TimeIntervalInv` cuts it to the invariant the same way, and
`TimeIntervalSplit` computes its input contribution without asking the
location's input set to hold the origin; `…Float` are the two at float zonotopes.

`JumpOfPoint`/`JumpIntersectionOfPoint` are the same pair at `OfPoint`, the weaker class
the offset actually needs — what lets `ConPolyZono`, having no `OfInterval`
instance, jump at all (#38).

`Jump`, `JumpOfPoint` and both `TimeInterval`s read nothing of the guard or
the invariant, so they leave that representation free. The three that call
`Intersection.intersection` cannot: `Intersection` is homogeneous, so they ask for it in `S` (#39).

At float zonotopes, which have no `Intersection` and no `Real.OfInterval`: the
cuts go through a box, `TimeIntervalInvFloat` to the invariant and
`GuardIntersectFloat` to a guard; `JumpFloat` resets; `LocationReachFloat` is a
stay's time-interval sets, and `ReachFloat` the automaton's, CORA's `reach`. `ReachGuard` is a
stay's sets up to leaving the invariant and their enclosure at a guard, its operators passed in.
-/
