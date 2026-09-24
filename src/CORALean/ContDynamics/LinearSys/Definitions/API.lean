import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSet
import CORALean.ContDynamics.LinearSys.Definitions.IntegralReachSet
import CORALean.ContDynamics.LinearSys.Definitions.IntegralTimeIntervalReachSet
import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
import CORALean.ContDynamics.LinearSys.Definitions.IntegralTrajectory
import CORALean.ContDynamics.LinearSys.Definitions.PerturbedTrajectory
import CORALean.ContDynamics.LinearSys.Definitions.PerturbedIntegralTrajectory
import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetForallExists
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.Definitions.IntegralBackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.Definitions.IntegralBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.Definitions.IntegralTimeIntervalBackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.Definitions.IntegralTimeIntervalBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.Definitions.IntegralTimeIntervalBackReachSetOfInput
import CORALean.ContDynamics.LinearSys.Definitions.ReachInner
import CORALean.ContDynamics.LinearSys.Definitions.StepInner
import CORALean.ContDynamics.LinearSys.Definitions.AutoState
import CORALean.ContDynamics.LinearSys.Definitions.ManualState
import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachState
import CORALean.ContDynamics.LinearSys.Definitions.MinBackReachState
import CORALean.ContDynamics.LinearSys.Definitions.TunedState
import CORALean.ContDynamics.LinearSys.Definitions.VerifyIter
import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
import CORALean.ContDynamics.LinearSys.Definitions.ReachParams

/-!
# What a continuous-time linear system means

The set the flow reaches in `ReachSet`, over an interval in
`TimeIntervalReachSet`, and under the weaker Carathéodory reading in
`IntegralReachSet`/`IntegralTimeIntervalReachSet`. `ClosedForm` is the
variation-of-constants formula; `IntegralTrajectory` is `Trajectory` over the
integral equation, `PerturbedTrajectory`/`PerturbedIntegralTrajectory` the
same with a second, independently-quantified disturbance signal.

The backward sets: `BackReachSetExistsForall`/`BackReachSetForallExists` at a
time point, `TimeIntervalBackReachSetExistsForall`/`ForallExists` over an
interval, and the `Integral...` families reading those over
`PerturbedIntegralTrajectory` instead. `IntegralTimeIntervalBackReachSetOfInput`
is the set under one fixed input signal, [1, Thm. 1]'s intersection target.

`ReachParams`/`ReachExact` are what `Reach` asks of it, homogeneous.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/
