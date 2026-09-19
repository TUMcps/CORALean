import CORALean.ContDynamics.LinearSys.AdaptTimeStep
import CORALean.ContDynamics.LinearSys.ClosedForm
import CORALean.ContDynamics.LinearSys.IntegralReachSet
import CORALean.ContDynamics.LinearSys.IntegralTimeIntervalReachSet
import CORALean.ContDynamics.LinearSys.IntegralTrajectory
import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.API
import CORALean.ContDynamics.LinearSys.Operations.API
import CORALean.ContDynamics.LinearSys.ReachSet
import CORALean.ContDynamics.LinearSys.StepConvergenceError
import CORALean.ContDynamics.LinearSys.StepError
import CORALean.ContDynamics.LinearSys.StepInner
import CORALean.ContDynamics.LinearSys.Theorems.API
import CORALean.ContDynamics.LinearSys.TimeIntervalReachSet

/-!
# Continuous-time linear systems, collected

The system and what it denotes in `LinearSys`, sampling in `Operations`, the
set the flow reaches in `ReachSet` and over an interval in `TimeIntervalReachSet`,
how far a step's enclosure exceeds it in `StepError`, that excess taken back off
in `StepInner`, the two halves of it that converge and decrease superlinearly
in `StepConvergenceError`, the closed form of a trajectory and what `reach` then
guarantees in `Theorems`.

Reachability holds at the sample times, by sampling into `LinearSysDT`, or, once
`e^{AΔt}` is only enclosed rather than computed, into `LinParamSysDT`. Between
the sample times it is open: that needs a set enclosing the curve over a step.
-/
