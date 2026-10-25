module

public import CORALean.ContDynamics.LinearSys.Definitions.IsAutoInvariantFloat
public import CORALean.ContDynamics.LinearSys.Definitions.AutoStateFloat
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.LinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBound
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSetExact
public import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
public import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalForm
public import CORALean.ContDynamics.LinearSys.Definitions.IsPerturbedTrajectory
public import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetExistsForallExact
public import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetForallExistsExact
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetExistsForallExact
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetForallExistsExact
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetOfInputExact
public import CORALean.ContDynamics.LinearSys.Definitions.ReachInner
public import CORALean.ContDynamics.LinearSys.Definitions.StepInner
public import CORALean.ContDynamics.LinearSys.Definitions.AutoState
public import CORALean.ContDynamics.LinearSys.Definitions.ManualState
public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachState
public import CORALean.ContDynamics.LinearSys.Definitions.MinBackReachState
public import CORALean.ContDynamics.LinearSys.Definitions.TimePointBound
public import CORALean.ContDynamics.LinearSys.Definitions.TimePointBoundOfInputReach
public import CORALean.ContDynamics.LinearSys.Definitions.TimePointWitness
public import CORALean.ContDynamics.LinearSys.Definitions.TunedState
public import CORALean.ContDynamics.LinearSys.Definitions.VerifyIter
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySpec
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySound
public import CORALean.ContDynamics.LinearSys.Definitions.VerifyIterFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySpecFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySoundFloat
public import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
public import CORALean.ContDynamics.LinearSys.Definitions.WithInput
public import CORALean.ContDynamics.LinearSys.Definitions.WithInputReachExact
public import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplit
public import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplitReachExact
public import CORALean.ContDynamics.LinearSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsReachFloatInputInvariant
public import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveOptions
public import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveState
public import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveStepInfo
public import CORALean.ContDynamics.LinearSys.Definitions.StepSets
public import CORALean.ContDynamics.LinearSys.Definitions.IsAdaptiveInvariant
public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
public import CORALean.ContDynamics.LinearSys.Definitions.ManualStateFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsManualInvariantFloat
public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloat
public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloatEncloses
public import CORALean.ContDynamics.LinearSys.Definitions.HeldInput
public import CORALean.ContDynamics.LinearSys.Definitions.HeldSim
public import CORALean.ContDynamics.LinearSys.Definitions.SupportLowerState
public import CORALean.ContDynamics.LinearSys.Definitions.HullPdf
public import CORALean.ContDynamics.LinearSys.Definitions.HullPdfInterval
public import CORALean.ContDynamics.LinearSys.Definitions.InputLaws
public import CORALean.ContDynamics.LinearSys.Definitions.InputLawsOver
public import CORALean.ContDynamics.LinearSys.Definitions.SupportUpperState
public import CORALean.ContDynamics.LinearSys.Definitions.VerifySearchState
public import CORALean.ContDynamics.LinearSys.Definitions.InputRemainderSet

/-!
# What a continuous-time linear system means

The set the Carathéodory runs reach in `ReachSetExact`, over an interval in
`TimeIntervalReachSetExact`. `ClosedForm` is the variation-of-constants formula;
`IsPerturbedTrajectory` a run with a second, independently-quantified disturbance signal.

The backward sets over it: `BackReachSetExistsForallExact`/`BackReachSetForallExistsExact`
at a time point, `TimeIntervalBackReachSetExistsForallExact`/`ForallExists` over an
interval. `TimeIntervalBackReachSetOfInputExact` is the set under one fixed input
signal, [1, Thm. 1]'s intersection target.

`ReachExact` is what `Reach` asks of it, homogeneous;
`WithInput`/`WithInputReachExact` the same with an input set holding the
origin, `WithInputSplit`/`WithInputSplitReachExact` with one anywhere.
`IsOrderAdmissibleFloat` is the order the float steps ask for,
`IsReachFloatInputInvariant` what `reachFloatInput`'s loop state owes, and
`ReachOptions` CORA's `options` for a reach run, `Δt` and the orders,
`ReachStepOptions` the two of them a scheme without order reduction reads.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/
