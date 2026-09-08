import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryStepOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToTrajectory
import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ToLinParam
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryToLinParam

/-!
# What `LinParamSys` gives, collected

`TimeIntervalStepOuter`/`ConstTrajectoryTimeIntervalOuter`: what the step
encloses, and where a constant-parameter run then is at every time of the step.
`ConstTrajectoryToLinearSys` is what the second rests on — with one matrix
fixed, the closed form of a `LinearSys` run applies unchanged.
`InputSolutionOuter` is the other half of a step, what the input contributes
over it, and `ConstTrajectoryStepOuter` puts the two together at the end of the
step.

`constTrajectory_toTrajectory`: CORA's `'constParam'` is a special case of
`'varParam'`, at the constant function. `ToLinParam`/`TrajectoryToLinParam`:
`LinearSys` is the constant-parameter instantiation at a point, in the
direction `OfPoint` gives — the converse needs the matrix set to be only that
point, which `OfPoint` does not say.
-/
