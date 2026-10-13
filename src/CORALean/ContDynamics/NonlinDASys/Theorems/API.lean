module

public import CORALean.ContDynamics.NonlinDASys.Theorems.ExistsLocalReduction
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachFloatOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachFloatCheckedEqSome
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionExactEq
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachYUnionSubsetImage
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryOfNonlinearSys
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToNonlinearSys
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryYEq
public import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonIterateSpec
public import CORALean.ContDynamics.NonlinDASys.Theorems.ConsistentInitialStateSpec
public import CORALean.ContDynamics.NonlinDASys.Theorems.SteadyStateSpec
public import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonTestFloatSound
public import CORALean.ContDynamics.NonlinDASys.Theorems.ConsistentInitialStateFloatRoot
public import CORALean.ContDynamics.NonlinDASys.Theorems.SteadyStateFloatRoot
public import CORALean.ContDynamics.NonlinDASys.Theorems.ExistsLagrangeRemainder
public import CORALean.ContDynamics.NonlinDASys.Theorems.SharedLagrangePointCounterexample
public import CORALean.ContDynamics.NonlinDASys.Theorems.AlgDeviationEq
public import CORALean.ContDynamics.NonlinDASys.Theorems.MemLinInclusion
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryDerivMemLinInclusion
public import CORALean.ContDynamics.NonlinDASys.Theorems.JointReachSetOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorCoraCounterexample
public import CORALean.ContDynamics.NonlinDASys.Theorems.OutputSetLinearCoraCounterexample
public import CORALean.ContDynamics.NonlinDASys.Theorems.OutputSetLinearOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToLinearSys
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachCoraCounterexample
public import CORALean.ContDynamics.NonlinDASys.Theorems.InitReachOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryShift
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinPointCertifiesOfSubset
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachRepeatSpec
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachLoopOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.AbstractionErrorAdaptiveOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachAtOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachAdaptiveOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachAdaptiveLoopOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachAdaptiveOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.EnlargeInterfaceInputSubset
public import CORALean.ContDynamics.NonlinDASys.Theorems.ComposeSubsystemsExact
public import CORALean.ContDynamics.NonlinDASys.Theorems.ComposeSubsystemsEqPreimage
public import CORALean.ContDynamics.NonlinDASys.Theorems.CompositionalLocalErrorCounterexample
public import CORALean.ContDynamics.NonlinDASys.Theorems.CompLocalErrorCoraCounterexample
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachCompCoraCounterexample
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachNextCompositionalSpec

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
