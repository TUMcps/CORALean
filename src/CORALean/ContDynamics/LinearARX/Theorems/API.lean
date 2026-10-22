module

public import CORALean.ContDynamics.LinearARX.Theorems.ComputeGOFloatOuter
public import CORALean.ContDynamics.LinearARX.Theorems.ComputeGOOutput
public import CORALean.ContDynamics.LinearARX.Theorems.Alg1EqReachWindowExact
public import CORALean.ContDynamics.LinearARX.Theorems.Alg2EqReachWindowExact
public import CORALean.ContDynamics.LinearARX.Theorems.Alg2NeReachWindowExact
public import CORALean.ContDynamics.LinearARX.Theorems.BextEqZero
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLe
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLt
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeSucc
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeSuccIndex
public import CORALean.ContDynamics.LinearARX.Theorems.EqSimulate
public import CORALean.ContDynamics.LinearARX.Theorems.OfObserverStep
public import CORALean.ContDynamics.LinearARX.Theorems.ReachOutExactEqImageBlock
public import CORALean.ContDynamics.LinearARX.Theorems.ReachOutExactEqSimulate
public import CORALean.ContDynamics.LinearARX.Theorems.ReachWindowExactEq
public import CORALean.ContDynamics.LinearARX.Theorems.ReachWindowExactNeProd
public import CORALean.ContDynamics.LinearARX.Theorems.SsReachEq
public import CORALean.ContDynamics.LinearARX.Theorems.StackEqTvp
public import CORALean.ContDynamics.LinearARX.Theorems.FeedMemInputSet
public import CORALean.ContDynamics.LinearARX.Theorems.OutputOuter
public import CORALean.ContDynamics.LinearARX.Theorems.ReachOuter
public import CORALean.ContDynamics.LinearARX.Theorems.SimulateMemReach
public import CORALean.ContDynamics.LinearARX.Theorems.SimulateMemSimulateBoxFloat
public import CORALean.ContDynamics.LinearARX.Theorems.SimulateIsTrajectory
public import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero
public import CORALean.ContDynamics.LinearARX.Theorems.Basic
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTStep
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTIsTrajectory
public import CORALean.ContDynamics.LinearARX.Theorems.OfCharpolyStep
public import CORALean.ContDynamics.LinearARX.Theorems.IdentifyBlocksMulVec
public import CORALean.ContDynamics.LinearARX.Theorems.IdentifyCandidateFit
public import CORALean.ContDynamics.LinearARX.Theorems.IdentifyCandidateLeastSquares
public import CORALean.ContDynamics.LinearARX.Theorems.IdentifyLeCandidate

/-!
# What the conversion guarantees

`ToLinearSysDTTrajectory` maps an ARX trajectory to a trajectory of the converted
system, through `ToLinearSysDTStep` and `FeedMemInputSet`; `ReachOuter` and
`OutputOuter` then read `LinearSysDT`'s guarantees back against the ARX outputs.
Everything is at `ℝ`: `Scalar` has no law relating a block matrix to its entries.

The ARMAX form (Lützow and Althoff, CDC 2023): `StackEqTvp` (Thm. 1) and the `Btilde` lemmas
(Lemmas 1-3) give `ReachWindowExactEq` (Eq. 12), which
`Alg1EqReachWindowExact`/`Alg2EqReachWindowExact` reach; `ReachWindowExactNeProd` and
`Alg2NeReachWindowExact` are where the paper is wrong.

`identify`: `IdentifyCandidateFit` (consistent data is reproduced), `IdentifyCandidateLeastSquares`
(any data) and `IdentifyLeCandidate` (the selected rank is no worse).
-/
