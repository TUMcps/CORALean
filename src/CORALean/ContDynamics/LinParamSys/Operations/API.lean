import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolution
import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagate
import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinParamSys.Operations.ExpEnclosure
import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZono
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZonoFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSum
import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTail
import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTailFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputTerm
import CORALean.ContDynamics.LinParamSys.Operations.InputTermZono
import CORALean.ContDynamics.LinParamSys.Operations.InputTermZonoFloat
import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolution
import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk
import CORALean.ContDynamics.LinParamSys.Operations.ReachUnion
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinParamSys.Operations.WithInputReachStepk
import CORALean.ContDynamics.LinParamSys.Operations.WithInputReachUnion
import CORALean.ContDynamics.LinParamSys.Operations.WithInputSplitReachStepk
import CORALean.ContDynamics.LinParamSys.Operations.WithInputSplitReachUnion
import CORALean.ContDynamics.LinParamSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStepFloat
import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosureFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Operations.SquaringsFloat
import CORALean.ContDynamics.LinParamSys.Operations.ExpSquaringFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat

/-!
# What a continuous-time linear system with a set-valued matrix computes

Two enclosures of what happens inside a step, at every matrix the system's set
holds at once: `InputSolution` for what the input adds, `TimeIntervalStep` for
where the homogeneous flow goes. `InputTerm` and `InputTaylorSum` are the exact
orders the first is built from. `ReachOrder`/`ReachUnion`/`WithInputReachUnion`/
`WithInputSplitReachUnion` are `Instances`', over windows: `ReachStepk` and
`ParticularSolution` carry the first window's sets to later ones by
`ExpEnclosure`, `e^{At_k}` at every member at once; `ConstInputSolution` and
`ConstPropagate` do the same for a split input set's constant half.

`DiscretizeEnclosure` is the step taken over a whole horizon instead: the
exponential of the box, handed to `LinParamSysDT` so its recursion runs it. `…Float` compute
these at float interval matrices, `ExpIntervalFloat` the box's exponential at an order
`ReachOrderFloat` finds; `ReachFloat` is `ReachUnion` by `ReachStepkFloat`'s scaling and squaring.

At `ℐ` throughout: every factor is an interval matrix, the exponential and the
correction matrix of a box being interval matrices themselves. `InputSolutionZono`
is [1, Prop. 3.6] instead, at a matrix zonotope: `InputTermZono` for its exact
linear and quadratic orders, `InputTaylorSumTail` for the interval-matrix orders
past them.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
