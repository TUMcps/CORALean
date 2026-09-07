import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInputReflected
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
import CORALean.ContDynamics.LinearSys.Theorems.ContinuousOnState
import CORALean.ContDynamics.LinearSys.Theorems.Discretize
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosure
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureReach
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeHorizon
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeMatZonotope
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeMatZonotopeReach
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
import CORALean.ContDynamics.LinearSys.Theorems.FlowIci
import CORALean.ContDynamics.LinearSys.Theorems.FlowIoi
import CORALean.ContDynamics.LinearSys.Theorems.HasDerivWithinAtExpNegMulVec
import CORALean.ContDynamics.LinearSys.Theorems.InputEqDerivWithin
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterConvexCompact
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizonInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetOuter
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
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral

/-!
# What `LinearSys` guarantees

The closed form of a trajectory, then the two enclosures built on it: `reach` at
the sample times and `timeIntervalStep` over a whole step. The rest are the
input-integral facts those two rest on.

Both enclosures are stated once, over `ConvexSet` and `CompactSet`, and name no
representation. `TimeIntervalOuterSplit` is the same: dropping `0 ∈ U` needs
only `Recentre` and `OfPoint`, which any representation with a centre has.

The `ReachSet` trio is the same guarantees stated of a set: every trajectory is
in `reachSet`, which is inside what `reach` and `timeIntervalStep` compute.

`Restrict` is what makes the time domain a parameter worth having: a guarantee
over one step applies to a run over all forward time by throwing the rest away.
Each statement asks for the window it speaks about, and only `discretize` and
the `reach` statements built on it ask for `Set.Ici 0`.

`DiscretizeEnclosure`/`DiscretizeEnclosureReach` are `Discretize`/`ReachOuter`
again, at `discretizeEnclosure` in place of `discretize`, where the exponential
is only enclosed rather than computed, and the `DiscretizeMatZonotope` pair is
the same at a matrix zonotope, which keeps what a box drops.
-/
