import CORALean.Real.ContDynamics.LinearSys.Theorems.Discretize
import CORALean.Real.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.Real.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.Real.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.Real.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.Real.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.Real.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.Real.ContDynamics.LinearSys.Theorems.WeightedIntegral

/-!
# What `LinearSys` guarantees

One file per guarantee, named after the theorem it states. Auxiliary lemmas a
proof needs carry the `aux_` prefix and are used nowhere else.
-/
