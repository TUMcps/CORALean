import CORALean.ContDynamics.NonlinParamSys.Theorems.ConstTrajectoryToTrajectory
import CORALean.ContDynamics.NonlinParamSys.Theorems.ToNonlinParam
import CORALean.ContDynamics.NonlinParamSys.Theorems.ToNonlinearSys
import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryOfNonlinearSys
import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryToNonlinParam
import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryToNonlinearSys

/-!
# What `NonlinParamSys` guarantees

`ConstTrajectoryToTrajectory` is the two trajectory readings' relation to each
other; `ToNonlinParam` and `TrajectoryToNonlinParam` are the embedding from a
plain nonlinear system, its parameter ignored; `ToNonlinearSys` and the two
`Trajectory…NonlinearSys` files are the other embedding, reading the parameter
as an extra input, in both directions.
-/
