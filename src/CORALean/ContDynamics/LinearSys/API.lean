import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.Definitions.API
import CORALean.ContDynamics.LinearSys.Instances
import CORALean.ContDynamics.LinearSys.MatExp.API
import CORALean.ContDynamics.LinearSys.Operations.API
import CORALean.ContDynamics.LinearSys.Theorems.API

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
the sample times it is `reach`, `Instances`' `Reach`: homogeneous, one
`timeIntervalStep` window per `Δt` of `[0, tFinal]`, each carried by `e^{A t_k}`.

Backward, `PerturbedTrajectory` is `Trajectory` with a second, independently
quantified signal `w`: `backReachSetForallExists` and `backReachSetExistsForall`
are Wetzlinger and Althoff's Def. 6 and Def. 7, minimal and maximal, each with
a `timeInterval...` sibling for the interval reading of the same definition.
`PerturbedIntegralTrajectory` reads those two runs as integral equations, the
way `IntegralTrajectory` reads `Trajectory`, and `integralBackReach...` are the
two sets over it — the reading in which Prop. 3 and Prop. 5 are equalities.
`minBackReachTimeInterval` is their Alg. 1, held to Thm. 1 in `Theorems`.
-/
