module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolution
public import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagate
public import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosure
public import CORALean.ContDynamics.LinParamSys.Operations.ExpEnclosure
public import CORALean.ContDynamics.LinParamSys.Operations.InputSet
public import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
public import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZono
public import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZonoFloat
public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSum
public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTail
public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTailFloat
public import CORALean.ContDynamics.LinParamSys.Operations.InputTerm
public import CORALean.ContDynamics.LinParamSys.Operations.InputTermZonoFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk
public import CORALean.ContDynamics.LinParamSys.Operations.ReachUnion
public import CORALean.ContDynamics.LinParamSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinParamSys.Operations.ToLinParam
public import CORALean.ContDynamics.LinParamSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalFloat
public import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumFloat
public import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Operations.SquaringsFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatChecked
public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalZono
public import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatInput
public import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagateFloat
public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalZonoFloat
public import CORALean.ContDynamics.LinParamSys.Operations.DependentHomSolLowOrder
public import CORALean.ContDynamics.LinParamSys.Operations.DependentLowOrder
public import CORALean.ContDynamics.LinParamSys.Operations.DependentHomSol
public import CORALean.ContDynamics.LinParamSys.Operations.InitReachInputDependence
public import CORALean.ContDynamics.LinParamSys.Operations.Canonical

/-!
# What a continuous-time linear system with a set-valued matrix computes

Two enclosures of what happens inside a step, at every matrix the system's set
holds at once: `InputSolution` for what the input adds, `TimeInterval` for
where the homogeneous flow goes. `InputTerm` and `InputTaylorSum` are the exact
orders the first is built from. `ReachOrder`/`ReachUnion` are `Instances`', over windows,
`ReachUnion` forming `B U ⊕ c` (`InputSet`) from CORA's `params.U` and `ReachStepkInput`
splitting it at its center: `ReachStepk` and `ParticularSolution` carry the first window's sets to
later ones by `ExpEnclosure`, `e^{At_k}` at every member at once; `ConstInputSolution` and
`ConstPropagate` do the same for the split input set's constant half.

`DiscretizeEnclosure` is the step taken over a whole horizon instead: the
exponential of the box, handed to `LinParamSysDT` so its recursion runs it. `…Float` compute
these at float interval matrices, `ExpIntervalFloat` the box's exponential at an order
`ReachOrderFloat` finds; `ReachFloat` is `ReachUnion` by `ReachStepkFloat`'s scaling and squaring.

At `ℐ` throughout: every factor is an interval matrix, the exponential and the
correction matrix of a box being interval matrices themselves. `InputSolutionZono`
is [1, Thm. 1] instead, at a matrix zonotope: `InputTermZono` for its exact
linear and quadratic orders, `InputTaylorSumTail` for the interval-matrix orders past them;
`InitReachInputDependence`/`DependentHomSol` CORA's first step with an input sharing its
parameters, `DependentLowOrder` corrected, `DependentHomSolLowOrder` as CORA computes it.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/
