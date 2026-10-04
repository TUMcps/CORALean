import CORALean.ContDynamics.LinearARX.Theorems.ComputeGOOutput
import CORALean.ContDynamics.LinearARX.Theorems.FeedMemFeedBox
import CORALean.ContDynamics.LinearARX.Theorems.Alg1EqReachWindow
import CORALean.ContDynamics.LinearARX.Theorems.Alg2EqReachWindow
import CORALean.ContDynamics.LinearARX.Theorems.Alg2NeReachWindow
import CORALean.ContDynamics.LinearARX.Theorems.BextEqZero
import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLe
import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLt
import CORALean.ContDynamics.LinearARX.Theorems.BtildeSucc
import CORALean.ContDynamics.LinearARX.Theorems.BtildeSuccIndex
import CORALean.ContDynamics.LinearARX.Theorems.EqSimulate
import CORALean.ContDynamics.LinearARX.Theorems.OfObserverStep
import CORALean.ContDynamics.LinearARX.Theorems.ReachOutEqImageBlock
import CORALean.ContDynamics.LinearARX.Theorems.ReachOutEqSimulate
import CORALean.ContDynamics.LinearARX.Theorems.ReachWindowEq
import CORALean.ContDynamics.LinearARX.Theorems.ReachWindowNeProd
import CORALean.ContDynamics.LinearARX.Theorems.SsReachEq
import CORALean.ContDynamics.LinearARX.Theorems.StackEqTvp
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
import CORALean.ContDynamics.LinearARX.Theorems.OfCharpolyStep

/-!
# What the conversion guarantees

`ToLinearSysDTTrajectory` maps an ARX trajectory to a trajectory of the converted
system, through `ToLinearSysDTStep` and `FeedMemInputSet`; `ReachOuter` and
`OutputOuter` then read `LinearSysDT`'s guarantees back against the ARX outputs.
Everything is at `ℝ`: `Scalar` has no law relating a block matrix to its entries.

The ARMAX form (Lützow and Althoff, CDC 2023): `StackEqTvp` (Thm. 1) and the `Btilde` lemmas
(Lemmas 1-3) give `ReachWindowEq` (Eq. 12), which `Alg1EqReachWindow`/`Alg2EqReachWindow`
reach; `ReachWindowNeProd` and `Alg2NeReachWindow` are where the paper is wrong.
-/
