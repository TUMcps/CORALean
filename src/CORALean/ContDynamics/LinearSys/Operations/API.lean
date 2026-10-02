import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStep
import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepOrder
import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepSearch
import CORALean.ContDynamics.LinearSys.Operations.AutoInit
import CORALean.ContDynamics.LinearSys.Operations.AutoReach
import CORALean.ContDynamics.LinearSys.Operations.AutoRun
import CORALean.ContDynamics.LinearSys.Operations.AutoStep
import CORALean.ContDynamics.LinearSys.Operations.AutoTuneDeltaT
import CORALean.ContDynamics.LinearSys.Operations.AutoTuneOrder
import CORALean.ContDynamics.LinearSys.Operations.AutoTuneSearch
import CORALean.ContDynamics.LinearSys.Operations.BundleReach
import CORALean.ContDynamics.LinearSys.Operations.ConstInputSolution
import CORALean.ContDynamics.LinearSys.Operations.DeltaReach
import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotope
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotopeFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
import CORALean.ContDynamics.LinearSys.Operations.GirardReach
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionInner
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionSet
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTail
import CORALean.ContDynamics.LinearSys.Operations.InputTerm
import CORALean.ContDynamics.LinearSys.Operations.ManualInit
import CORALean.ContDynamics.LinearSys.Operations.ManualReach
import CORALean.ContDynamics.LinearSys.Operations.ManualRun
import CORALean.ContDynamics.LinearSys.Operations.ManualStep
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZ
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachInit
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachMu
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachPoly
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachRun
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachStep
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachTimeInterval
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachInit
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachP
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachRun
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachStep
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachSupport
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachTimeInterval
import CORALean.ContDynamics.LinearSys.Operations.ParticularSolution
import CORALean.ContDynamics.LinearSys.Operations.PostDelta
import CORALean.ContDynamics.LinearSys.Operations.PropagateInputSolution
import CORALean.ContDynamics.LinearSys.Operations.Reach
import CORALean.ContDynamics.LinearSys.Operations.ReachAdmissible
import CORALean.ContDynamics.LinearSys.Operations.ReachError
import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInputStep
import CORALean.ContDynamics.LinearSys.Operations.ReachInnerRep
import CORALean.ContDynamics.LinearSys.Operations.ReachInputError
import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachStepk
import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFree
import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachTimePointWrappingFreeFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFree
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloatInput
import CORALean.ContDynamics.LinearSys.Operations.SampleTimeFloat
import CORALean.ContDynamics.LinearSys.Operations.SquaringsFloat
import CORALean.ContDynamics.LinearSys.Operations.StepErrorBox
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureError
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepEps
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepError
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
import CORALean.ContDynamics.LinearSys.Operations.TimePoint
import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepFloat
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerRep
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepRemainderError
import CORALean.ContDynamics.LinearSys.Operations.TunedInit
import CORALean.ContDynamics.LinearSys.Operations.TunedReach
import CORALean.ContDynamics.LinearSys.Operations.TunedRun
import CORALean.ContDynamics.LinearSys.Operations.TunedStep
import CORALean.ContDynamics.LinearSys.Operations.Verify
import CORALean.ContDynamics.LinearSys.Operations.VerifyRun
import CORALean.ContDynamics.LinearSys.Operations.VerifyStep
import CORALean.ContDynamics.LinearSys.Operations.WithInputReach
import CORALean.ContDynamics.LinearSys.Operations.WithInputReachStepk
import CORALean.ContDynamics.LinearSys.Operations.WithInputSplitReach
import CORALean.ContDynamics.LinearSys.Operations.WithInputSplitReachStepk

/-!
# What a continuous-time linear system computes

Sampling in `Discretize`, and then three enclosures of what happens inside a
step: `InputSolution` for what the input adds, `TimeIntervalStep` for where the
homogeneous flow goes, `DeltaReach` for how far it has moved from where it
started. `StepInput` and `InputReach` are the exact quantities
those two are measured against; `StepInputConst` is `StepInput` at one held
vector rather than a whole signal.

`TimeIntervalStepEps` is `TimeIntervalStep` with its truncation order chosen
from an admissible error, one knob of adaptive tuning and not the algorithm.
`DiscretizeEnclosure` is `Discretize` again, its matrix only enclosed: `e^{AΔt}`
is transcendental, so where the exponential itself cannot be computed the
result is a `LinParamSysDT` over an interval matrix rather than a `LinearSysDT`, real or float.

`InputTaylorSumTail` is `InputTaylorSum` from order `1` instead of `0`, the split Wetzlinger et
al.'s adaptive reachability needs, which keeps order `0` out as a term of its own.
`ReachStepk`/`Reach` are CORA's default, recursive scheme, `ReachAdmissible` raising its `η`
until admissible, `Instances`' own; `ReachStepkWrappingFree`/`ReachWrappingFree`/`ReachOrder` are
the wrapping-free scheme's, kept but no longer `Instances`', `WithInputReach…` with
`ParticularSolution`, `WithInputSplitReach…` with `ConstInputSolution` too; `PostDelta` is CORA's
`postΔ`, `DeltaReach` plus an uncertain input's `InputSolution`, [1, Sec. 4.1]. `…Float` run them
in `𝕋`, each named after its scheme, `…FloatInput` with an input `B U` and `InputSolutionFloat`.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/
