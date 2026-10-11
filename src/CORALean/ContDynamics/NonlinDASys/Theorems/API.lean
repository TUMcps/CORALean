import CORALean.ContDynamics.NonlinDASys.Theorems.ExistsLocalReduction
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachFloatCheckedEqSome
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionExactEq
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachYUnionSubsetImage
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryOfNonlinearSys
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToNonlinearSys
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryYEq
import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonIterateSpec
import CORALean.ContDynamics.NonlinDASys.Theorems.ConsistentInitialStateSpec
import CORALean.ContDynamics.NonlinDASys.Theorems.SteadyStateSpec
import CORALean.ContDynamics.NonlinDASys.Theorems.ExistsLagrangeRemainder
import CORALean.ContDynamics.NonlinDASys.Theorems.SharedLagrangePointCounterexample
import CORALean.ContDynamics.NonlinDASys.Theorems.AlgDeviationEq
import CORALean.ContDynamics.NonlinDASys.Theorems.MemLinInclusion
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryDerivMemLinInclusion
import CORALean.ContDynamics.NonlinDASys.Theorems.JointReachSetOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorCoraCounterexample
import CORALean.ContDynamics.NonlinDASys.Theorems.OutputSetLinearCoraCounterexample
import CORALean.ContDynamics.NonlinDASys.Theorems.OutputSetLinearOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToLinearSys
import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.InitReachOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryShift
import CORALean.ContDynamics.NonlinDASys.Theorems.LinPointCertifiesOfSubset
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachRepeatSpec
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachLoopOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachOuter

/-!
# What `NonlinDASys` guarantees

`ExistsLocalReduction` is the implicit function theorem for an index-1 system, a reduced
model locally; `TrajectoryToNonlinearSys` and `TrajectoryOfNonlinearSys` are the
correspondence with the reduced ordinary system, `ReachUnionExactEq` its consequence for the
reachable set, and `ReachUnionOuter` what `reachUnion` guarantees through it,
`ReachYUnionSubsetImage` the algebraic part, `TrajectoryYEq` its pointwise form.
-/
