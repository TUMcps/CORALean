import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErr
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLin
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyCandidates
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrSolInf
import CORALean.ContDynamics.NonlinearSys.Operations.Gain
import CORALean.ContDynamics.NonlinearSys.Operations.GainDim
import CORALean.ContDynamics.NonlinearSys.Operations.GainMax
import CORALean.ContDynamics.NonlinearSys.Operations.GainOrder
import CORALean.ContDynamics.NonlinearSys.Operations.GainOrderDim
import CORALean.ContDynamics.NonlinearSys.Operations.GlobalAbstrErr
import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContDynamics.NonlinearSys.Operations.LinPoint
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPoly
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachCora1D
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrAdaptiveCora1D
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptErrLoopCora1D
import CORALean.ContDynamics.NonlinearSys.Operations.OptimalDeltatCora
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachAdaptiveCora1D
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
import CORALean.ContDynamics.NonlinearSys.Operations.LocalAbstrErr
import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatError
import CORALean.ContDynamics.NonlinearSys.Operations.RelinDeltaReach
import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach
import CORALean.ContDynamics.NonlinearSys.Operations.RelinTimeInterval
import CORALean.ContDynamics.NonlinearSys.Operations.TuneAbstrOrder
import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrInit
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrStep
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrRun
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrReach
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptInit
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptLinPass
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptStep
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptRun
import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrInit
import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrStep
import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrRun
import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrReach
import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainSearch
import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGain
import CORALean.ContDynamics.NonlinearSys.Operations.InterpGain
import CORALean.ContDynamics.NonlinearSys.Operations.ReachSizeEstimate
import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatSearch
import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltat
import CORALean.ContDynamics.NonlinearSys.Operations.LinStepLinInput
import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatInit
import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltat
import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachInit
import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachStep
import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachRun
import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachReach
import CORALean.ContDynamics.NonlinearSys.Operations.ReachUnion
import CORALean.ContDynamics.NonlinearSys.Operations.LinInputFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
import CORALean.ContDynamics.NonlinearSys.Operations.ReachFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RegionFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunAtFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepAtFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat
import CORALean.ContDynamics.NonlinearSys.Operations.SlopeRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyFloat
import CORALean.ContDynamics.NonlinearSys.Operations.HalfMat
import CORALean.ContDynamics.NonlinearSys.Operations.VarInputsFloat
import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachRunFloat
import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloat
import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloatChecked
import CORALean.ContDynamics.NonlinearSys.Operations.SplitReach
import CORALean.ContDynamics.NonlinearSys.Operations.Identify
import CORALean.ContDynamics.NonlinearSys.Operations.IdentifyCandidate
import CORALean.ContDynamics.NonlinearSys.Operations.ReachFloatChecked
import CORALean.ContDynamics.NonlinearSys.Operations.InterpGainFloat
import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainSearchFloat
import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainFloat
import CORALean.ContDynamics.NonlinearSys.Operations.GainMaxFloat
import CORALean.ContDynamics.NonlinearSys.Operations.ReachSizeEstimateFloat
import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatSearchFloat
import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatFloat
import CORALean.ContDynamics.NonlinearSys.Operations.TuneAbstrOrderFloat
import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatInitFloat
import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatFloat
import CORALean.ContDynamics.NonlinearSys.Operations.OrderStepFloat
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptLinPassFloat
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptStepFloat
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptRunFloat
import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrStepFloat
import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrRunFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainderFloat
import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffStep
import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffLoop
import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiff
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInnerErr
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInner
import CORALean.ContDynamics.NonlinearSys.Operations.ReachInnerMinkdiffLoop
import CORALean.ContDynamics.NonlinearSys.Operations.ReachInnerMinkdiff
import CORALean.ContDynamics.NonlinearSys.Operations.ReachInnerScalingCora1D

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
`LinReachPoly` runs both from a start set; `LinReachCora1D` is CORA's `'lin'` step in 1D, as
printed, `LinReachAdaptiveCora1D` its adaptive first step, `ReachInnerScalingCora1D` its `'scale'`
inner approximation; `AbstrErr` is the other paper's one-step error from `postΔ` and `VarInputs`.

`LocalAbstrErr` and `GlobalAbstrErr` measure what a step and a run add to the exact answer,
`AbstrSolInf` the untruncated set of those errors, `GainDim`/`Gain`/`GainMax`/`GainOrder` how much
of its width a smaller step keeps. The `…Float` files are the float runs: `ReachFloat` from a
`FloatModel`, `ReachAlgFloat` at `alg = 'lin'` or `'poly'` from a `FloatHessModel`.
-/
