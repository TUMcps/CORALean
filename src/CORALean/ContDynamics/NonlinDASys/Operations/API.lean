import CORALean.ContDynamics.NonlinDASys.Operations.ReachUnion
import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloat
import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloatChecked
import CORALean.ContDynamics.NonlinDASys.Operations.ToNonlinearSys
import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialState
import CORALean.ContDynamics.NonlinDASys.Operations.SteadyState
import CORALean.ContDynamics.NonlinDASys.Operations.NewtonTestFloat
import CORALean.ContDynamics.NonlinDASys.Operations.FloatModelStackRes
import CORALean.ContDynamics.NonlinDASys.Operations.FloatModelStackJac
import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialStateFloat
import CORALean.ContDynamics.NonlinDASys.Operations.SteadyStateFloat
import CORALean.ContDynamics.NonlinDASys.Operations.JointReachSet
import CORALean.ContDynamics.NonlinDASys.Operations.LinError
import CORALean.ContDynamics.NonlinDASys.Operations.LinErrorCora
import CORALean.ContDynamics.NonlinDASys.Operations.CompLocalErrorCora
import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinearCora
import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinear
import CORALean.ContDynamics.NonlinDASys.Operations.LinReach
import CORALean.ContDynamics.NonlinDASys.Operations.LinReachCora
import CORALean.ContDynamics.NonlinDASys.Operations.InitReach
import CORALean.ContDynamics.NonlinDASys.Operations.ReachRepeat
import CORALean.ContDynamics.NonlinDASys.Operations.ReachLoop
import CORALean.ContDynamics.NonlinDASys.Operations.Reach
import CORALean.ContDynamics.NonlinDASys.Operations.AbstractionErrorAdaptive
import CORALean.ContDynamics.NonlinDASys.Operations.AdaptPassLinPoint
import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAt
import CORALean.ContDynamics.NonlinDASys.Operations.ErrorLoopAdaptive
import CORALean.ContDynamics.NonlinDASys.Operations.PassAdaptive
import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAdaptive
import CORALean.ContDynamics.NonlinDASys.Operations.ReachAdaptiveLoop
import CORALean.ContDynamics.NonlinDASys.Operations.ReachAdaptive
import CORALean.ContDynamics.NonlinDASys.Operations.EnlargeInterfaceInput
import CORALean.ContDynamics.NonlinDASys.Operations.ComposeSubsystems
import CORALean.ContDynamics.NonlinDASys.Operations.ReachNextCompositional

/-!
# What `NonlinDASys` computes

`ToNonlinearSys` eliminates the algebraic variable through a reduced model; `ReachUnion` runs
the reduced system's re-linearization loop. `ConsistentInitialStateFloat` and
`SteadyStateFloat` run CORA's Newton loops in floats and keep the end point only when
`NewtonTestFloat` certifies a zero near it; `FloatModelStackRes` and `FloatModelStackJac` read a
float model on the stacked state `(x, y)`. `EnlargeInterfaceInput`, `ComposeSubsystems` and
`ReachNextCompositional` are the compositional step of Althoff's power-system analysis.
-/
