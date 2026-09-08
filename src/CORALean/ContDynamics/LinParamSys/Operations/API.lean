import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSum
import CORALean.ContDynamics.LinParamSys.Operations.InputTerm
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep

/-!
# What a continuous-time linear system with a set-valued matrix computes

Two enclosures of what happens inside a step, at every matrix the system's set
holds at once: `InputSolution` for what the input adds, `TimeIntervalStep` for
where the homogeneous flow goes. `InputTerm` and `InputTaylorSum` are the exact
orders the first is built from.

At `ℐ` throughout: every factor is an interval matrix, the exponential and the
correction matrix of a box being interval matrices themselves.
-/
