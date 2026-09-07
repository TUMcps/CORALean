import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToTrajectory
import CORALean.ContDynamics.LinParamSys.Theorems.ToLinParam
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryToLinParam

/-!
# What `LinParamSys` gives, collected

`constTrajectory_toTrajectory`: CORA's `'constParam'` is a special case of
`'varParam'`, at the constant function. `ToLinParam`/`TrajectoryToLinParam`:
`LinearSys` is the constant-parameter instantiation at a point, in the
direction `OfPoint` gives — the converse needs the matrix set to be only that
point, which `OfPoint` does not say.
-/
