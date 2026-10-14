module

public import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachExistsOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachForallInner
public import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetExistsPreimage
public import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetExistsTrajectory
public import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetForallTrajectory
public import CORALean.ContDynamics.LinearSysDT.Theorems.ComputeGOFloatOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ComputeGOOutput
public import CORALean.ContDynamics.LinearSysDT.Theorems.ComputeGOState
public import CORALean.ContDynamics.LinearSysDT.Theorems.HeldToTrajectory
public import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfOutput
public import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfSeparating
public import CORALean.ContDynamics.LinearSysDT.Theorems.MemSimulateBoxIn
public import CORALean.ContDynamics.LinearSysDT.Theorems.NotHoldsOfSimulate
public import CORALean.ContDynamics.LinearSysDT.Theorems.OutputOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachBigO
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachBigOConZonotope
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachFloatSubsetReachSetAddError
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachFloatZeroMemError
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachInnerFloatInner
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLe
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLeConZonotope
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrdersConstEqReach
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrdersOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetBound
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetConvex
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetInnerOfOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetIsCompact
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetSubsetReach
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetWitness
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.API
public import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateMemReach
public import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateMemSimulateBoxFloat
public import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateTrajectory
public import CORALean.ContDynamics.LinearSysDT.Theorems.TrajectoryStateEq
public import CORALean.ContDynamics.LinearSysDT.Theorems.IdentifyCandidateFit
public import CORALean.ContDynamics.LinearSysDT.Theorems.IdentifyLeCandidate
public import CORALean.ContDynamics.LinearSysDT.Theorems.DiscretizeToLinearSys
public import CORALean.ContDynamics.LinearSysDT.Theorems.ExpIntegralToLinearSys
public import CORALean.ContDynamics.LinearSysDT.Theorems.IsConformDynOfModel
public import CORALean.ContDynamics.LinearSysDT.Theorems.ErrMatFloatMem
public import CORALean.ContDynamics.LinearSysDT.Theorems.ObservePropagationFloatOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ObserveIntervalFloatOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ObserveStepOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ObserveStripBasedOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSpecCoraFinalCounterexample
public import CORALean.ContDynamics.LinearSysDT.Theorems.TrajectoryCanonical
public import CORALean.ContDynamics.LinearSysDT.Theorems.CanonicalTrajectoryTrajectoryCanonical

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
