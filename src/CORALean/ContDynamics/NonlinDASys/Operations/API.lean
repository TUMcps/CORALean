module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloat
public import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloatChecked
public import CORALean.ContDynamics.NonlinDASys.Operations.Basic
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
public import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialState
public import CORALean.ContDynamics.NonlinDASys.Operations.SteadyState
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonTestFloat
public import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialStateFloat
public import CORALean.ContDynamics.NonlinDASys.Operations.SteadyStateFloat
public import CORALean.ContDynamics.NonlinDASys.Operations.JointReachSet
public import CORALean.ContDynamics.NonlinDASys.Operations.LinError
public import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinear
public import CORALean.ContDynamics.NonlinDASys.Operations.LinReach
public import CORALean.ContDynamics.NonlinDASys.Operations.InitReach
public import CORALean.ContDynamics.NonlinDASys.Operations.ReachRepeat
public import CORALean.ContDynamics.NonlinDASys.Operations.ReachLoop
public import CORALean.ContDynamics.NonlinDASys.Operations.Reach
public import CORALean.ContDynamics.NonlinDASys.Operations.AbstractionErrorAdaptive
public import CORALean.ContDynamics.NonlinDASys.Operations.AdaptPassLinPoint
public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAt
public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAdaptive
public import CORALean.ContDynamics.NonlinDASys.Operations.ReachAdaptiveLoop
public import CORALean.ContDynamics.NonlinDASys.Operations.ReachAdaptive
public import CORALean.ContDynamics.NonlinDASys.Operations.EnlargeInterfaceInput
public import CORALean.ContDynamics.NonlinDASys.Operations.ComposeSubsystems
public import CORALean.ContDynamics.NonlinDASys.Operations.ReachNextCompositional
public import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinearFloat

/-!
# What `NonlinDASys` computes

`ToNonlinearSys` eliminates the algebraic variable through a reduced model; `ReachUnion` runs
the reduced system's re-linearization loop. `ConsistentInitialStateFloat` and
`SteadyStateFloat` run CORA's Newton loops in floats and keep the end point only when
`NewtonTestFloat` certifies a zero near it; `FloatModelStackRes` and `FloatModelStackJac` read a
float model on the stacked state `(x, y)`. `EnlargeInterfaceInput`, `ComposeSubsystems` and
`ReachNextCompositional` are the compositional step of Althoff's power-system analysis.
-/
