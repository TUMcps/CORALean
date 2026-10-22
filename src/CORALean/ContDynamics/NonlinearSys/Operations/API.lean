module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErr
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLin
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrSolInf
public import CORALean.ContDynamics.NonlinearSys.Operations.Gain
public import CORALean.ContDynamics.NonlinearSys.Operations.GainDim
public import CORALean.ContDynamics.NonlinearSys.Operations.GainOrder
public import CORALean.ContDynamics.NonlinearSys.Operations.GainOrderDim
public import CORALean.ContDynamics.NonlinearSys.Operations.GlobalAbstrErr
public import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPoint
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPoly
public import CORALean.ContDynamics.NonlinearSys.Operations.LinearEmbedding
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSys.Operations.LocalAbstrErr
public import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatError
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinDeltaReach
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinTimeInterval
public import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrReach
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptInit
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptStep
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptRun
public import CORALean.ContDynamics.NonlinearSys.Operations.CenterAbstrReach
public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGain
public import CORALean.ContDynamics.NonlinearSys.Operations.InterpGain
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinStepLinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatInit
public import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltat
public import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachReach
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInputFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RegionFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunAtFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepAtFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.SlopeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.VarInputsFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloatChecked
public import CORALean.ContDynamics.NonlinearSys.Operations.SplitReach
public import CORALean.ContDynamics.NonlinearSys.Operations.Identify
public import CORALean.ContDynamics.NonlinearSys.Operations.IdentifyCandidate
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachFloatChecked
public import CORALean.ContDynamics.NonlinearSys.Operations.InterpGainFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OrderStepFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptLinPassFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptStepFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptRunFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.CenterAbstrStepFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.CenterAbstrRunFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainderFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffStep
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiff
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerCurvatureError
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerAbstrErr
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerLagrangeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInner
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachInnerMinkdiff

/-!
# What a linearization computes

The two halves of one linearization: `Linearize` is the linear system, and `LinInput` the set its
input has to range over for the two to agree. Neither mentions a derivative — what the split costs
is an `AbstractionError` certificate, not a bound on `f`. `PrecompStatError` is CORA's
`priv_precompStatError`, computing the second-order term instead of boxing it.

`RelinReach` is what a sequence of steps computes: one linear recursion step per linearization, the
set reached at a step's end the next one's initial set. `RelinTimeInterval` is the same step over
its whole interval, and `ReachUnion` the union of those steps as `Reach` runs them, `none` once a
run-time region test fails; `RelinDeltaReach` is CORA's `Rdiff`. `AbstrErrLin` is CORA's
`priv_abstrerr_lin` at `tensorOrder = 2`: the error box a second-order expansion leaves, data here
and certified in `Theorems`. `LagrangeRemainder` is the same one order up, once the quadratic term
is subtracted exactly rather than boxed. `AbstrErrPolySearch` is `linReach`'s while loop for
`alg = 'poly'`, a fuel-bounded search over the candidates `AbstrErrPolyCandidates` computes, and
`LinReachPoly` runs both from a start set. As printed: `LinReachCora1D` CORA's `'lin'` step in 1D,
`LinReachTensor3Cora2D` at `tensorOrder = 3` in 2D, `LinReachAdaptiveCora1D` the adaptive step,
`ReachInnerScalingCora1D` `'scale'`, `OutputSetCora` outputs. `AbstrErr`/`VarInputs`: other paper.

`LocalAbstrErr` and `GlobalAbstrErr` measure what a step and a run add to the exact answer,
`AbstrSolInf` the untruncated set of those errors, `GainDim`/`Gain`/`GainMax`/`GainOrder` how much
of its width a smaller step keeps. The `…Float` files are the float runs: `ReachFloat` from a
`FloatModel`, `ReachAlgFloat` at `alg = 'lin'` or `'poly'` from a `FloatHessModel`.
-/
