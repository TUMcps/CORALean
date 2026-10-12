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
import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonTestFloatSound
import CORALean.ContDynamics.NonlinDASys.Theorems.ConsistentInitialStateFloatRoot
import CORALean.ContDynamics.NonlinDASys.Theorems.SteadyStateFloatRoot
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
import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachCoraCounterexample
import CORALean.ContDynamics.NonlinDASys.Theorems.InitReachOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryShift
import CORALean.ContDynamics.NonlinDASys.Theorems.LinPointCertifiesOfSubset
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachRepeatSpec
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachLoopOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.AbstractionErrorAdaptiveOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachAtOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachAdaptiveOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachAdaptiveLoopOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachAdaptiveOuter
import CORALean.ContDynamics.NonlinDASys.Theorems.EnlargeInterfaceInputSubset
import CORALean.ContDynamics.NonlinDASys.Theorems.ComposeSubsystemsExact
import CORALean.ContDynamics.NonlinDASys.Theorems.ComposeSubsystemsEqPreimage
import CORALean.ContDynamics.NonlinDASys.Theorems.CompositionalLocalErrorCounterexample
import CORALean.ContDynamics.NonlinDASys.Theorems.CompLocalErrorCoraCounterexample
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachNextCompositionalSpec

/-!
# What `NonlinDASys` guarantees

`ExistsLocalReduction` is the implicit function theorem for an index-1 system, a reduced
model locally; `TrajectoryToNonlinearSys` and `TrajectoryOfNonlinearSys` are the
correspondence with the reduced ordinary system, `ReachUnionExactEq` its consequence for the
reachable set, and `ReachUnionOuter` what `reachUnion` guarantees through it,
`ReachYUnionSubsetImage` the algebraic part, `TrajectoryYEq` its pointwise form.
`NewtonTestFloatSound` is what a passed float Newton test proves, a unique zero nearby, and
`ConsistentInitialStateFloatRoot` and `SteadyStateFloatRoot` its two uses.
`ComposeSubsystemsExact` and `ComposeSubsystemsEqPreimage` are the join of subsystem sets,
`ReachNextCompositionalSpec` what the compositional loop certifies, and
`CompositionalLocalErrorCounterexample` that local `C F⁻¹` blocks miss the coupling.
-/
