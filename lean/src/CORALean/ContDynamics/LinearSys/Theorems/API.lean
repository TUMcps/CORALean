import CORALean.ContDynamics.LinearSys.Theorems.Discretize
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral

/-!
# What `LinearSys` guarantees

One file per guarantee, named after the theorem it states. Auxiliary lemmas a
proof needs carry the `aux_` prefix and are used nowhere else.
-/
