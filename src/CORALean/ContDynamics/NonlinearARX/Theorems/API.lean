import CORALean.ContDynamics.NonlinearARX.Theorems.ComputeGOOutput
import CORALean.ContDynamics.NonlinearARX.Theorems.OutputOuter
import CORALean.ContDynamics.NonlinearARX.Theorems.OutputSelMulVec
import CORALean.ContDynamics.NonlinearARX.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateTrajectory
import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateMemSimulateBoxFloat
import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateMemReach
import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTStep
import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTTrajectory
import CORALean.ContDynamics.NonlinearARX.Theorems.FloatModelEnclosesToNonlinearSysDTFloat

/-!
# What the conversion guarantees

`ToNonlinearSysDTTrajectory` maps an ARX trajectory to a trajectory of the converted
system, through `ToNonlinearSysDTStep`; `ReachOuter` and `OutputOuter` then read
`NonlinearSysDT.reach_outer` back against the ARX outputs. `ComputeGOOutput` is the exact
identity of the output-error linearization.
-/
