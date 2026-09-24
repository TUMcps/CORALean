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
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionZonoOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinParamSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ToLinParam
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryNormDriftLe
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryNormLe
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryTimeIntervalOuterInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryToLinParam

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

`TrajectoryToLinearSys` is the same move at `'varParam'`, at the cost of an
input set enlarged by the parameter drift: `TrajectoryNormLe` bounds the
state a priori by Gronwall, `TrajectoryNormDriftLe` turns that into the
radius the enlarged set needs, `TrajectoryTimeIntervalOuter…` the step.
The `…Split` pair drops `0 ∈ U` by splitting the input set, and
`ConstTrajectoryDiscretizeEnclosure`/`…MemReach` carry one step to a whole
horizon through `LinParamSysDT.reach` — together, [1, Alg. 4].
`ConstTrajectoryToTrajectory`, `ToLinParam` and `TrajectoryToLinParam` are the
readings' conversions: `'constParam'` is `'varParam'` at a constant function,
and `LinearSys` is `LinParamSys` at a point. `InputSolutionZonoOuter` is
`InputSolutionOuter` at a matrix zonotope instead, and
`ReachOrderAdmissible`/`ReachUnionOuter` are `Instances`' guarantee.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
