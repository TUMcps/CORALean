module

public import CORALean.ContDynamics.NonlinearARX.Theorems.ComputeGOOutput
public import CORALean.ContDynamics.NonlinearARX.Theorems.ComputeGOFloatOuter
public import CORALean.ContDynamics.NonlinearARX.Theorems.OutputOuter
public import CORALean.ContDynamics.NonlinearARX.Theorems.OutputSelMulVec
public import CORALean.ContDynamics.NonlinearARX.Theorems.ReachOuter
public import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateTrajectory
public import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateMemSimulateBoxFloat
public import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateMemReach
public import CORALean.ContDynamics.NonlinearARX.Theorems.ReachStepCoraHoldsOfError
public import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTStep
public import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTTrajectory
public import CORALean.ContDynamics.NonlinearARX.Theorems.FloatModelEnclosesToNonlinearSysDTFloat
public import CORALean.ContDynamics.NonlinearARX.Theorems.FloatJacModelEnclosesToNonlinearSysDTFloat

/-!
# What the conversion guarantees

`ToNonlinearSysDTTrajectory` maps an ARX trajectory to a trajectory of the converted
system, through `ToNonlinearSysDTStep`; `ReachOuter` and `OutputOuter` then read
`NonlinearSysDT.reach_outer` back against the ARX outputs. `ComputeGOOutput` is the exact
identity of the output-error linearization.
-/
