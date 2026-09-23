import CORALean.ContDynamics.LinearSys.Operations.DeltaReach
import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotope
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionInner
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionSet
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTail
import CORALean.ContDynamics.LinearSys.Operations.InputTerm
import CORALean.ContDynamics.LinearSys.Operations.PostDelta
import CORALean.ContDynamics.LinearSys.Operations.PropagateInputSolution
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepEps
import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
import CORALean.ContDynamics.LinearSys.Operations.ReachError
import CORALean.ContDynamics.LinearSys.Operations.ReachInputError
import CORALean.ContDynamics.LinearSys.Operations.StepErrorBox
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepError
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureError
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepRemainderError
import CORALean.ContDynamics.LinearSys.Operations.ReachInnerRep
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerRep
import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepOrder
import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepSearch
import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStep
import CORALean.ContDynamics.LinearSys.Operations.AutoTuneOrder
import CORALean.ContDynamics.LinearSys.Operations.AutoTuneSearch
import CORALean.ContDynamics.LinearSys.Operations.AutoTuneDeltaT

/-!
# What a continuous-time linear system computes

Sampling in `Discretize`, and then three enclosures of what happens inside a
step: `InputSolution` for what the input adds, `TimeIntervalStep` for where the
homogeneous flow goes, `DeltaReach` for how far it has moved from where it
started. `StepInput` and `InputReach` are the exact quantities
those two are measured against; `StepInputConst` is `StepInput` at one held
vector rather than a whole signal.

`TimeIntervalStepEps` is `TimeIntervalStep` with its truncation order chosen
from an admissible error rather than given, which is one knob of adaptive
parameter tuning and not the algorithm.

`DiscretizeEnclosure` is `Discretize` again, its matrix only enclosed: `e^{AΔt}`
is transcendental, so where the exponential itself cannot be computed the
result is a `LinParamSysDT` over an interval matrix rather than a `LinearSysDT`.

`InputTaylorSumTail` is `InputTaylorSum` from order `1` instead of `0`, the
split Wetzlinger et al.'s adaptive reachability needs, which keeps order `0`
out as a term of its own.

`PostDelta` is CORA's `postΔ`: `DeltaReach` plus what a constant uncertain
input set contributes as `InputSolution`, named for [1, Sec. 4.1].

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/
