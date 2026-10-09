import CORALean.ContDynamics.NonlinearARX.NonlinearARX
import CORALean.ContDynamics.NonlinearARX.Definitions.FloatModel
import CORALean.ContDynamics.NonlinearARX.Operations.API
import CORALean.ContDynamics.NonlinearARX.Theorems.API

/-!
# Nonlinear ARX models, collected

The model and its trajectories in `NonlinearARX`, the conversion to `NonlinearSysDT`
in `Operations`, and in `Theorems` that every ARX trajectory is one of the converted
system, so that its reach encloses the ARX outputs.

Left: ARX-form reach, `simulate`, `identify`, the converse of the
trajectory correspondence, and CORA's cached derivative tensors (the converted
system's `LinStep` carries them). Unlike `LinearARX`, the conversion keeps the
input in a stacked vector of dimension `dim_u (p+1)`, so no input dependency is lost.
-/
