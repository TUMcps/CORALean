import CORALean.ContDynamics.Reach.Definitions.InputParams
import CORALean.ContDynamics.Reach.Definitions.Params

/-!
# How a reach operation takes its arguments

`sys.reach params options`, CORA's `reach(sys, params, options)`. `params` is
the problem, shared by every system class: `Params` (`R0`, `tStart`, `tFinal`) or
`InputParams` (`R0`, `U`, `tStart`, `tFinal`). `options` is the algorithm, one
`ReachOptions` per family beside its system, with CORA's field names
(`timeStep`, `taylorTerms`, `zonotopeOrder`) and only the fields it reads;
`linAlg` and `reductionTechnique` are which function is called and the
representation's `Reduce` instance, so a field could only disagree with the code.

A continuous run derives its step count `(tFinal - tStart) / timeStep` itself,
exactly (`Reach.steps`, through `ToRat`), and is `none` unless it is a natural
number, CORA's integer-steps check. A side condition on the options a caller can
decide is a field with a default proof (`hZonotopeOrder`); one a run can check it
checks, returning `none` (`0 < timeStep`); what needs the system stays a theorem
hypothesis. The sets the runs enclose (`reachSet`, `Trajectory`) stay positional:
they are the mathematics, not CORA's interface.
-/
