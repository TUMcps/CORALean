import CORALean.ContDynamics.LinearSys.Theorems.Discretize
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterZonotope
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterSplitZonotope
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterZonotope
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral

/-!
# What `LinearSys` guarantees

The closed form of a trajectory, then the two enclosures built on it: `reach` at
the sample times and `timeIntervalStep` over a whole step. The rest are the
input-integral facts those two rest on.
-/
