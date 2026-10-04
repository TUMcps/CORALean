import CORALean.HybridDynamics.Theorems.CalcBasisBoxOrthogonal
import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.FlowOuterInputSolution
import CORALean.HybridDynamics.Theorems.FlowOuterSplit
import CORALean.HybridDynamics.Theorems.FlowOuterFloat
import CORALean.HybridDynamics.Theorems.FlowOuterSplitFloat
import CORALean.HybridDynamics.Theorems.GuardIntersectFloatOuter
import CORALean.HybridDynamics.Theorems.HoldsAllOfInvariant
import CORALean.HybridDynamics.Theorems.HoldsOfCheck
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.HoldsOfRunOn
import CORALean.HybridDynamics.Theorems.InvariantOfEnclosure
import CORALean.HybridDynamics.Theorems.InvariantOfEnclosureCut
import CORALean.HybridDynamics.Theorems.InvariantOnOfInvariant
import CORALean.HybridDynamics.Theorems.JumpIntersectionOuter
import CORALean.HybridDynamics.Theorems.JumpOuter
import CORALean.HybridDynamics.Theorems.JumpOuterConZonotope
import CORALean.HybridDynamics.Theorems.JumpOfPointOuter
import CORALean.HybridDynamics.Theorems.JumpFloatOuter
import CORALean.HybridDynamics.Theorems.JumpFloatOuterConZonotope
import CORALean.HybridDynamics.Theorems.JumpIntersectionOfPointOuter
import CORALean.HybridDynamics.Theorems.LinearEmbedding
import CORALean.HybridDynamics.Theorems.LocationReachFloatOuter
import CORALean.HybridDynamics.Theorems.ReachFloatOuter
import CORALean.HybridDynamics.Theorems.ReachLocationsOuter
import CORALean.HybridDynamics.Theorems.ReachSetOuter
import CORALean.HybridDynamics.Theorems.ReachSetEqIUnionRunUntil
import CORALean.HybridDynamics.Theorems.ReachSetSubsetInvariant
import CORALean.HybridDynamics.Theorems.ReachSetSubsetReachFloat
import CORALean.HybridDynamics.Theorems.ResetImageSubset
import CORALean.HybridDynamics.Theorems.RunExistsRunOn
import CORALean.HybridDynamics.Theorems.RunIffExistsRunUntil
import CORALean.HybridDynamics.Theorems.RunOnOuter
import CORALean.HybridDynamics.Theorems.RunOnToRun
import CORALean.HybridDynamics.Theorems.RunOuter
import CORALean.HybridDynamics.Theorems.RunUntilMono
import CORALean.HybridDynamics.Theorems.RunUntilToRunOn
import CORALean.HybridDynamics.Theorems.TimeIntervalInvOuter
import CORALean.HybridDynamics.Theorems.TimeIntervalInvFloatOuter
import CORALean.HybridDynamics.Theorems.TrajectoryMemIccRight
import CORALean.HybridDynamics.Theorems.NonlinearResetEvaluateToNonlinearReset
import CORALean.HybridDynamics.Theorems.NonlinearResetEvaluateMemEvaluateFloat
import CORALean.HybridDynamics.Theorems.TransitionToNonlinearResetFloatEncloses
import CORALean.HybridDynamics.Theorems.NonlinearResetFoldlUpdateOfNotMem
import CORALean.HybridDynamics.Theorems.NonlinearResetLiftOfNotMem
import CORALean.HybridDynamics.Theorems.NonlinearResetLiftBind
import CORALean.HybridDynamics.Theorems.NonlinearResetFloatModelEnclosesLift
import CORALean.HybridDynamics.Theorems.NonlinearResetEvaluateSynchronize
import CORALean.HybridDynamics.Theorems.NonlinearResetFloatModelEnclosesSynchronize
import CORALean.HybridDynamics.Theorems.LinearResetLiftBind
import CORALean.HybridDynamics.Theorems.LinearResetLiftOfNotMem
import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeApply
import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeFloatOffsetOuter
import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeFloatOuter
import CORALean.HybridDynamics.Theorems.HasDerivAtSdcFlow
import CORALean.HybridDynamics.Theorems.MemConstFlowHitSet
import CORALean.HybridDynamics.Theorems.MemHitSet
import CORALean.HybridDynamics.Theorems.TendstoSdcFlowError
import CORALean.HybridDynamics.Theorems.HasDerivAtHitJacobian
import CORALean.HybridDynamics.Theorems.HasDerivAtHitPoint
import CORALean.HybridDynamics.Theorems.LocationPotIntComplete
import CORALean.HybridDynamics.Theorems.LocationPotOutOuter
import CORALean.HybridDynamics.Theorems.GuardIntersectNondetFloatOuter
import CORALean.HybridDynamics.Theorems.GuardIntersectPolytopeFloatOuter
import CORALean.HybridDynamics.Theorems.TransitionConvGuardExact
import CORALean.HybridDynamics.Theorems.TransitionGuard2PolytopeExact
import CORALean.HybridDynamics.Theorems.TransitionGuard2PolytopeInterval
import CORALean.HybridDynamics.Theorems.TransitionGuard2PolytopeOuter
import CORALean.HybridDynamics.Theorems.TransitionGuard2PolytopeReset
import CORALean.HybridDynamics.Theorems.TransitionSynchronizeGuardExact
import CORALean.HybridDynamics.Theorems.TransitionSynchronizeReset
import CORALean.HybridDynamics.Theorems.TransitionSynchronizeTargetApply
import CORALean.HybridDynamics.Theorems.TransitionSynchronizeTargetCORACounterexample
import CORALean.HybridDynamics.Theorems.ResetTaylorMem
import CORALean.HybridDynamics.Theorems.ResetTaylorCounterexample
import CORALean.HybridDynamics.Theorems.TrajectoryErrorOuter
import CORALean.HybridDynamics.Theorems.IdentGuardEq
import CORALean.HybridDynamics.Theorems.SplitTreeExecutable
import CORALean.HybridDynamics.Theorems.LinearResetResolveApply
import CORALean.HybridDynamics.Theorems.NonlinearResetResolveApply
import CORALean.HybridDynamics.Theorems.NonlinearResetFloatModelEnclosesResolve
import CORALean.HybridDynamics.Theorems.NonlinearResetResolveCORACounterexample
import CORALean.HybridDynamics.Theorems.NonlinearResetResolveCORASharedInputs

/-!
# What a hybrid run guarantees, collected

Read in the order a step is taken. `LinearEmbedding` makes a stay a linear trajectory,
`FlowOuter` encloses it and `TimeIntervalInvOuter` cuts that to the invariant; `JumpOuter`
intersects with the guard and applies the reset, `ResetImageSubset` restates it as a set
inclusion, `JumpOuterConZonotope` discharges the one hypothesis `JumpOuter` leaves without an
`Intersection` instance, and `JumpIntersectionOuter` is the case where one discharges it.
`RunOuter` chains the two by induction on the run, and `HoldsOfRun`/`HoldsAllOfInvariant` turn
the result into an answer, one specification or a list of them. `ReachSetOuter`/
`ReachLocationsOuter`/`ReachSetSubsetInvariant` restate the same at a set of runs.

The bounded-horizon reading: `RunOnToRun`/`RunExistsRunOn` relate `RunOn` to `Run`, `RunOnOuter`
is `RunOuter` at an index, `HoldsOfRunOn` its corollary, and `InvariantOnOfInvariant` reads an
`Invariant` as the constant-family case. By `RunIffExistsRunUntil`, `RunUntil` is a `Run` with a
duration bound; `ReachFloatOuter`/`ReachSetSubsetReachFloat` enclose such runs in floats.

`FlowOuterInputSolution` computes `FlowOuter`'s input contribution rather than
naming it, `FlowOuterSplit` without asking `0 ∈ ℓ.U`, `…Float` the same in floats, and
`InvariantOfEnclosureCut` is the criterion those buy, cut to `ℓ.inv` and with a
model: uncut, `InvariantOfEnclosure`'s `hflow` has none under a nonzero drift.

`JumpOfPointOuter`/`JumpIntersectionOfPointOuter` read the same two guarantees at
`OfPoint`, which `ConPolyZono` has and `OfInterval` it does not (#38).
-/
