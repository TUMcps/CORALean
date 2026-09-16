import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInputReflected
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
import CORALean.ContDynamics.LinearSys.Theorems.ContinuousOnState
import CORALean.ContDynamics.LinearSys.Theorems.DeltaReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.DeltaReachOuterInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.Discretize
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosure
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureReach
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeHorizon
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeMatZonotope
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeMatZonotopeReach
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeReachSetSubsetInputReach
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.ExistsTimeIntervalStepErrorLt
import CORALean.ContDynamics.LinearSys.Theorems.ExistsTimeIntervalStepInnerInner
import CORALean.ContDynamics.LinearSys.Theorems.ExistsTimePointStepErrorLt
import CORALean.ContDynamics.LinearSys.Theorems.ExistsTimePointStepInnerInner
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
import CORALean.ContDynamics.LinearSys.Theorems.FlowIci
import CORALean.ContDynamics.LinearSys.Theorems.FlowIoi
import CORALean.ContDynamics.LinearSys.Theorems.HasDerivWithinAtExpNegMulVec
import CORALean.ContDynamics.LinearSys.Theorems.InputEqDerivWithin
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.InputReachConvex
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.IntegralReachSetEq
import CORALean.ContDynamics.LinearSys.Theorems.IntegralReachSetSubset
import CORALean.ContDynamics.LinearSys.Theorems.IntegralReachSetSuperset
import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimeIntervalBound
import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimeIntervalReachSetEqUnion
import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimeIntervalReachSetSubsetSegmentsSum
import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimeIntervalWitness
import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimePointBound
import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimePointWitness
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import CORALean.ContDynamics.LinearSys.Theorems.PostDeltaOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterConvexCompact
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizonInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSubsetImageInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSubsetReach
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSubsetTimeIntervalInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.Restrict
import CORALean.ContDynamics.LinearSys.Theorems.StepInputConstEq
import CORALean.ContDynamics.LinearSys.Theorems.StepInputEqShifted
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.StepInputShift
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
import CORALean.ContDynamics.LinearSys.Theorems.StepSubsetHorizon
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterConvexCompact
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalBound
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetEqUnion
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetSubsetSegmentsSum
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetSubsetTimeIntervalInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepEpsOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepInnerInner
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepOuterSegments
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepSubsetAddError
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepSubsetInitialAddError
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalWitness
import CORALean.ContDynamics.LinearSys.Theorems.TimePointBound
import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepInnerInner
import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepSubsetAddError
import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepSubsetConstInputAddError
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryDeltaReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryIntegralTrajectory
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral

/-!
# What `LinearSys` guarantees

The closed form of a trajectory, then the three enclosures built on it: `reach`
at the sample times, `timeIntervalStep` over a whole step, and `deltaReach` over
the differences that step spans — what CORA's polynomialization variant measures
its next abstraction error on. The rest are the input-integral facts they use.

The first two are stated once, over `ConvexSet` and `CompactSet`, and name no
representation. `TimeIntervalOuterSplit` is the same: dropping `0 ∈ U` needs
only `Recentre` and `OfPoint`, which any representation with a centre has.

The `ReachSet` and `TimeIntervalReachSet` trios state the same guarantees of a
set; `_eq_iUnion` ties the latter to a union of the former, `SubsetAddError`
runs a step backwards, `Exists…Lt` shrinks its error, `SegmentsSum` feeds
`TimeIntervalBound` a genuine `+`/`segments`, and `TimeIntervalWitness` its dual.

`Restrict` is what makes the time domain a parameter worth having: a guarantee
over one step applies to a run over all forward time by throwing the rest away.
Only `discretize` and the `reach` statements built on it ask for `Set.Ici 0`.

`DiscretizeEnclosure`/`DiscretizeEnclosureReach` are `Discretize`/`ReachOuter`
enclosed rather than computed; `DiscretizeMatZonotope` is the same at a matrix
zonotope, and `PostDeltaOuter` is `DeltaReachOuterInputSolution` again, `postΔ`'s name.
-/
