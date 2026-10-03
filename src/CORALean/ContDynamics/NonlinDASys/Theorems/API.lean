import CORALean.ContDynamics.NonlinDASys.Theorems.ExistsLocalReduction
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionExactEq
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachYUnionSubsetImage
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryOfNonlinearSys
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToNonlinearSys
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryYEq
import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonIterateSpec
import CORALean.ContDynamics.NonlinDASys.Theorems.ConsistentInitialStateSpec
import CORALean.ContDynamics.NonlinDASys.Theorems.SteadyStateSpec

/-!
# What `NonlinDASys` guarantees

`ExistsLocalReduction` is the implicit function theorem for an index-1 system, a reduced
model locally; `TrajectoryToNonlinearSys` and `TrajectoryOfNonlinearSys` are the
correspondence with the reduced ordinary system, `ReachUnionExactEq` its consequence for the
reachable set, and `ReachUnionOuter` what `reachUnion` guarantees through it,
`ReachYUnionSubsetImage` the algebraic part, `TrajectoryYEq` its pointwise form.
-/
