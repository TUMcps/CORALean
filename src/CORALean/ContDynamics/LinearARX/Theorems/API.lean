import CORALean.ContDynamics.LinearARX.Theorems.ComputeGOOutput
import CORALean.ContDynamics.LinearARX.Theorems.FeedMemFeedBox
import CORALean.ContDynamics.LinearARX.Theorems.FeedMemInputSet
import CORALean.ContDynamics.LinearARX.Theorems.OutputEqMulVec
import CORALean.ContDynamics.LinearARX.Theorems.OutputOuter
import CORALean.ContDynamics.LinearARX.Theorems.OutputPowInputMat
import CORALean.ContDynamics.LinearARX.Theorems.ReachOuter
import CORALean.ContDynamics.LinearARX.Theorems.SimulateMemReach
import CORALean.ContDynamics.LinearARX.Theorems.SimulateMemSimulateBoxFloat
import CORALean.ContDynamics.LinearARX.Theorems.SimulateTrajectory
import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero
import CORALean.ContDynamics.LinearARX.Theorems.SumBlock
import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTStep
import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTTrajectory

/-!
# What the conversion guarantees

`ToLinearSysDTTrajectory` maps an ARX trajectory to a trajectory of the converted
system, through `ToLinearSysDTStep` and `FeedMemInputSet`; `ReachOuter` and
`OutputOuter` then read `LinearSysDT`'s guarantees back against the ARX outputs.
Everything is at `ℝ`: `Scalar` has no law relating a block matrix to its entries.
-/
