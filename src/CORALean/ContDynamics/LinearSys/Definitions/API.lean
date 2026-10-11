import CORALean.ContDynamics.LinearSys.Definitions.AutoInvariantFloat
import CORALean.ContDynamics.LinearSys.Definitions.AutoStateFloat
import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSet
import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalForm
import CORALean.ContDynamics.LinearSys.Definitions.ClassicalTrajectory
import CORALean.ContDynamics.LinearSys.Definitions.PerturbedTrajectory
import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetForallExists
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetOfInput
import CORALean.ContDynamics.LinearSys.Definitions.ReachInner
import CORALean.ContDynamics.LinearSys.Definitions.StepInner
import CORALean.ContDynamics.LinearSys.Definitions.AutoState
import CORALean.ContDynamics.LinearSys.Definitions.ManualState
import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachState
import CORALean.ContDynamics.LinearSys.Definitions.MinBackReachState
import CORALean.ContDynamics.LinearSys.Definitions.TunedState
import CORALean.ContDynamics.LinearSys.Definitions.VerifyIter
import CORALean.ContDynamics.LinearSys.Definitions.VerifySpec
import CORALean.ContDynamics.LinearSys.Definitions.VerifySound
import CORALean.ContDynamics.LinearSys.Definitions.VerifyIterFloat
import CORALean.ContDynamics.LinearSys.Definitions.VerifySpecFloat
import CORALean.ContDynamics.LinearSys.Definitions.VerifySoundFloat
import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
import CORALean.ContDynamics.LinearSys.Definitions.WithInput
import CORALean.ContDynamics.LinearSys.Definitions.WithInputReachExact
import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplit
import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplitReachExact
import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinearSys.Definitions.ReachFloatInputInvariant
import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveOptions
import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveState
import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveStepInfo
import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveInvariant
import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
import CORALean.ContDynamics.LinearSys.Definitions.ManualStateFloat
import CORALean.ContDynamics.LinearSys.Definitions.ManualInvariantFloat
import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloat
import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloatEncloses
import CORALean.ContDynamics.LinearSys.Definitions.HeldInput
import CORALean.ContDynamics.LinearSys.Definitions.HeldSim
import CORALean.ContDynamics.LinearSys.Definitions.SupportLowerState
import CORALean.ContDynamics.LinearSys.Definitions.HullPdf
import CORALean.ContDynamics.LinearSys.Definitions.HullPdfInterval
import CORALean.ContDynamics.LinearSys.Definitions.InputLaws
import CORALean.ContDynamics.LinearSys.Definitions.InputLawsOver
import CORALean.ContDynamics.LinearSys.Definitions.SupportUpperState
import CORALean.ContDynamics.LinearSys.Definitions.VerifySearchState

/-!
# What a continuous-time linear system means

The set the Carathéodory runs reach in `ReachSet`, over an interval in
`TimeIntervalReachSet`. `ClosedForm` is the variation-of-constants formula;
`ClassicalTrajectory` the derivative-everywhere run, the special case a nonlinear
or parameter-varying run is linearized to; `PerturbedTrajectory` a run with a
second, independently-quantified disturbance signal.

The backward sets over it: `BackReachSetExistsForall`/`BackReachSetForallExists`
at a time point, `TimeIntervalBackReachSetExistsForall`/`ForallExists` over an
interval. `TimeIntervalBackReachSetOfInput` is the set under one fixed input
signal, [1, Thm. 1]'s intersection target.

`ReachExact` is what `Reach` asks of it, homogeneous;
`WithInput`/`WithInputReachExact` the same with an input set holding the
origin, `WithInputSplit`/`WithInputSplitReachExact` with one anywhere.
`OrderAdmissibleFloat` is the order the float steps ask for,
`ReachFloatInputInvariant` what `reachFloatInput`'s loop state owes, and
`ReachOptions` CORA's `options` for a reach run, `timeStep` and the orders,
`ReachStepOptions` the two of them a scheme without order reduction reads.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/
