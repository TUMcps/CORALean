module

public import CORALean.ContDynamics.NonlinearARX.NonlinearARX
public import CORALean.ContDynamics.NonlinearARX.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinearARX.Definitions.FloatJacModel
public import CORALean.ContDynamics.NonlinearARX.Operations.API
public import CORALean.ContDynamics.NonlinearARX.Theorems.API
public import CORALean.ContDynamics.NonlinearARX.Counterexamples.API

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
