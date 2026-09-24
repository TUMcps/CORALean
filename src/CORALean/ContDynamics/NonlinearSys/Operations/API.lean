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

/-!
# What a linearization computes

The two halves of one linearization: `Linearize` is the linear system, and
`LinInput` the set its input has to range over for the two to agree. Neither
mentions a derivative — what the split costs is an `AbstractionError`
certificate, not a bound on `f`. `PrecompStatError` is CORA's
`priv_precompStatError`, computing the second-order term instead of boxing it.

`RelinReach` is what a sequence of steps computes: one linear recursion step per linearization, the
set reached at a step's end the next one's initial set. `RelinTimeInterval` is the same step over
its whole interval, and `ReachUnion` the union of those steps as `Reach` runs them, `none` once a
run-time region test fails; `RelinDeltaReach` is CORA's `Rdiff`. `AbstrErrLin` is CORA's
`priv_abstrerr_lin` at `tensorOrder = 2`: the error box a second-order expansion leaves, data here
and certified in `Theorems`. `LagrangeRemainder` is the same one order up, once the quadratic term
is subtracted exactly rather than boxed. `AbstrErrPolySearch` is `linReach`'s while loop for
`alg = 'poly'`, a fuel-bounded search over the candidates `AbstrErrPolyCandidates` computes, and
`LinReachPoly` runs both from a start set. `AbstrErr` is the other paper's `abstrErr`, one step's
whole error out of `postΔ`, `VarInputs` and the latter.

`LocalAbstrErr` and `GlobalAbstrErr` measure what a step and a run add to the exact answer.
`AbstrSolInf` is the untruncated set of those errors, `GainDim` and `Gain` how much of its width a
smaller step keeps, `GainMax` that ratio off two boxes, `GainOrder` the limit order.
-/
