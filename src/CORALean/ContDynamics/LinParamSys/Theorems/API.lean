import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryDiscretizeEnclosure
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryDiscretizeEnclosureMemReach
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryInputSolutionTimeIntervalOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryInputSolutionTimeIntervalOuterSplit
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryStepOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalOuterInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalOuterSplit
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToTrajectory
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstPropagate
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpEnclosure
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolutionZonoFloat
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolution
import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionZonoOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.SmulPowMemInputTermZonoFloat
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ToLinParam
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryNormDriftLe
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryNormLe
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalOuterInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryToLinParam
import CORALean.ContDynamics.LinParamSys.Theorems.WithInputReachUnionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.WithInputSplitReachUnionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpIntervalFloat
import CORALean.ContDynamics.LinParamSys.Theorems.MapMEqSome
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepFloatOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalFloatOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryDiscretizeEnclosureFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryDiscretizeEnclosureFloatMemReach
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Theorems.SquaringsFloatSpec
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolutionFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ReachFloatInputOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstPropagateFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ReachFloatInputSplitOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpSquaringFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkFloatOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ReachFloatCheckedEqSome
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsMeasurableParam
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsIntegralEq
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsMemExpIntervalEnclosure
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimePointOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalStepOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsIntegralEqOfMeasurable
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalStepOuterInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalStepFloatOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalStepFloatOuterInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepZonoOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalZonoOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalStepIntervalOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepZonoFloatOuter
import CORALean.ContDynamics.LinParamSys.Theorems.DependentHomSolLowOrderCounterexample

/-!
# What `LinParamSys` gives, collected

`TimeIntervalStepOuter`/`ConstTrajectoryTimeIntervalOuter`: what the step
encloses, and where a constant-parameter run then is at every time of the step.
`ConstTrajectoryToLinearSys` is what the second rests on — with one matrix
fixed, the closed form of a `LinearSys` run applies unchanged.
`InputSolutionOuter` is the other half of a step, `ConstTrajectoryStepOuter`
puts the two together at its end, and `InputReachSubsetInputSolution` with
`ConstTrajectoryInputSolutionTimeIntervalOuter` extend that half to every time
of the step once `0 ∈ U`; `…TimeIntervalOuterInputSolution` is the whole step.

`TrajectoryTimeIntervalStepOuter`/`…TimePointOuter` are CORA's own `'varParam'` step, input-free,
through `TrajectoryExistsIntegralEq`/`…MeasurableParam`, `…InputSolution` with an
input, `…FloatOuter` at the float step; or `TrajectoryToLinearSys`
pays the drift as input, `TrajectoryNormLe`/`…NormDriftLe` bounding it by Gronwall.
The `…Split` pair drops `0 ∈ U` by splitting the input set, and
`ConstTrajectoryDiscretizeEnclosure`/`…MemReach` carry one step to a whole
horizon through `LinParamSysDT.reach` — together, [1, Alg. 4].
`ConstTrajectoryToTrajectory`, `ToLinParam` and `TrajectoryToLinParam` convert: `'constParam'`
is `'varParam'` at a constant, `LinearSys` `LinParamSys` at a point. `InputSolutionZonoOuter`
is `InputSolutionOuter` at a matrix zonotope instead, `…ZonoOuter` the step there, and
`ReachOrderAdmissible`/`ReachUnionOuter`/`WithInputReachUnionOuter` are `Instances`'.
`…Float…` are the same guarantees of the float operations, at float interval matrices.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
