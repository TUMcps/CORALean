import CORALean.ContDynamics.LinearSys.AdaptTimeStep
import CORALean.ContDynamics.LinearSys.AutoTuneDeltaT
import CORALean.ContDynamics.LinearSys.AutoTuneReach
import CORALean.ContDynamics.LinearSys.BackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.BackReachSetForallExists
import CORALean.ContDynamics.LinearSys.ClosedForm
import CORALean.ContDynamics.LinearSys.IntegralBackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.IntegralBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.IntegralReachSet
import CORALean.ContDynamics.LinearSys.IntegralTimeIntervalBackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.IntegralTimeIntervalBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.IntegralTimeIntervalBackReachSetOfInput
import CORALean.ContDynamics.LinearSys.IntegralTimeIntervalReachSet
import CORALean.ContDynamics.LinearSys.IntegralTrajectory
import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.ManualReach
import CORALean.ContDynamics.LinearSys.MatExp.API
import CORALean.ContDynamics.LinearSys.MaxBackReachTimeInterval
import CORALean.ContDynamics.LinearSys.MinBackReachTimeInterval
import CORALean.ContDynamics.LinearSys.Operations.API
import CORALean.ContDynamics.LinearSys.PerturbedIntegralTrajectory
import CORALean.ContDynamics.LinearSys.PerturbedTrajectory
import CORALean.ContDynamics.LinearSys.ReachError
import CORALean.ContDynamics.LinearSys.ReachInner
import CORALean.ContDynamics.LinearSys.ReachInputError
import CORALean.ContDynamics.LinearSys.ReachSet
import CORALean.ContDynamics.LinearSys.StepConvergenceError
import CORALean.ContDynamics.LinearSys.StepError
import CORALean.ContDynamics.LinearSys.StepErrorBox
import CORALean.ContDynamics.LinearSys.StepInner
import CORALean.ContDynamics.LinearSys.Theorems.API
import CORALean.ContDynamics.LinearSys.TimeIntervalBackReachSetExistsForall
import CORALean.ContDynamics.LinearSys.TimeIntervalBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.TimeIntervalReachSet
import CORALean.ContDynamics.LinearSys.TunedReach
import CORALean.ContDynamics.LinearSys.Verify

/-!
# Continuous-time linear systems, collected

The system and what it denotes in `LinearSys`, sampling in `Operations`, the
set the flow reaches in `ReachSet` and over an interval in `TimeIntervalReachSet`,
how far a step's enclosure exceeds it in `StepError`, as a zonotope in
`StepErrorBox`, that excess taken back off in `StepInner`, and over a whole
sampled run, accumulated in `ReachError`, in `ReachInner`; the two halves of it
that converge and decrease superlinearly in `StepConvergenceError`, the closed
form of a trajectory and what `reach` then guarantees in `Theorems`.

Reachability holds at the sample times, by sampling into `LinearSysDT`, or, once
`e^{AΔt}` is only enclosed rather than computed, into `LinParamSysDT`. Between
the sample times it is open: that needs a set enclosing the curve over a step.

Backward, `PerturbedTrajectory` is `Trajectory` with a second, independently
quantified signal `w`: `backReachSetForallExists` and `backReachSetExistsForall`
are Wetzlinger and Althoff's Def. 6 and Def. 7, minimal and maximal, each with
a `timeInterval...` sibling for the interval reading of the same definition.
`PerturbedIntegralTrajectory` reads those two runs as integral equations, the
way `IntegralTrajectory` reads `Trajectory`, and `integralBackReach...` are the
two sets over it — the reading in which Prop. 3 and Prop. 5 are equalities.
`minBackReachTimeInterval` is their Alg. 1, held to Thm. 1 in `Theorems`.
-/
