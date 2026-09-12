import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZono
import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSum
import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTail
import CORALean.ContDynamics.LinParamSys.Operations.InputTerm
import CORALean.ContDynamics.LinParamSys.Operations.InputTermZono
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep

/-!
# What a continuous-time linear system with a set-valued matrix computes

Two enclosures of what happens inside a step, at every matrix the system's set
holds at once: `InputSolution` for what the input adds, `TimeIntervalStep` for
where the homogeneous flow goes. `InputTerm` and `InputTaylorSum` are the exact
orders the first is built from.

`DiscretizeEnclosure` is the step taken over a whole horizon instead: the
exponential of the box, handed to `LinParamSysDT` so its recursion runs it.

At `ℐ` throughout: every factor is an interval matrix, the exponential and the
correction matrix of a box being interval matrices themselves. `InputSolutionZono`
is [1, Prop. 3.6] instead, at a matrix zonotope: `InputTermZono` for its exact
linear and quadratic orders, `InputTaylorSumTail` for the interval-matrix orders
past them.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
