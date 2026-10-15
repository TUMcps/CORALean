module

public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContDynamics.Reach.Definitions.Params

/-!
# How a reach operation takes its arguments

`sys.reach params options`, CORA's `reach(sys, params, options)`. `params` is
the problem, shared by every system class: `Params` (`X₀`, CORA's `R0`, `tStart`,
`tFinal`) or `InputParams` (`X₀`, `U`, `tStart`, `tFinal`). `options` is the algorithm, one
`ReachOptions` per family beside its system, with the paper's names for
CORA's `timeStep`, `taylorTerms`, `zonotopeOrder` (`Δt`, `η`, `ρ`) and only the fields it
reads;
`linAlg` and `reductionTechnique` are which function is called and the
representation's `Reduce` instance, so a field could only disagree with the code.

A continuous run derives its step count `(tFinal - tStart) / Δt` itself,
exactly (`Reach.steps`, through `ToRat`), and is `none` unless it is a natural
number, CORA's integer-steps check. A side condition on the options a caller can
decide is a field with a default proof (`hZonotopeOrder`); one a run can check it
checks, returning `none` (`0 < timeStep`); what needs the system stays a theorem
hypothesis. The sets the runs enclose (`reachSet`, `IsTrajectory`) stay positional:
they are the mathematics, not CORA's interface.
-/
