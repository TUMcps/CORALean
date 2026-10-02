import CORALean.ContDynamics.NonlinearARX.Theorems.OutputOuter
import CORALean.ContDynamics.NonlinearARX.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTStep
import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTTrajectory

/-!
# What the conversion guarantees

`ToNonlinearSysDTTrajectory` maps an ARX trajectory to a trajectory of the converted
system, through `ToNonlinearSysDTStep`; `ReachOuter` and `OutputOuter` then read
`NonlinearSysDT.reach_outer` back against the ARX outputs.
-/
