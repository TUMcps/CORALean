module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.Definitions.API
public import CORALean.ContDynamics.LinearSys.Instances
public import CORALean.ContDynamics.LinearSys.Krylov.API
public import CORALean.ContDynamics.LinearSys.MatExp.API
public import CORALean.ContDynamics.LinearSys.Operations.API
public import CORALean.ContDynamics.LinearSys.Theorems.API

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
the sample times it is `reach`, `Instances`' `Reach`: one `timeIntervalStep` window
per `Δt`, carried by `e^{A t_k}`, plus at `WithInput` the input accumulated so far.

A trajectory is Carathéodory — the integral equation — so `reachSet` *is*
`e^{tA} R₀ ⊕ inputReach U t` (`reachSet_eq`) and a witness there is reached;
`CanonicalClassicalTrajectory.trajectory` admits every derivative-everywhere run.
Backward, `PerturbedTrajectory` is `Trajectory` with a second, independently
quantified signal `w`: `backReachSetForallExists` and `backReachSetExistsForall`
are Wetzlinger and Althoff's Def. 6 and Def. 7, each with a `timeInterval...`
sibling, the reading in which Prop. 3 and Prop. 5 are equalities.
`minBackReachTimeInterval` is their Alg. 2, held to Thm. 1 in `Theorems`.
-/
