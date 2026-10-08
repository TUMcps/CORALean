import CORALean.ContDynamics.NonlinDASys.Operations.ReachUnion
import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloat
import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloatChecked
import CORALean.ContDynamics.NonlinDASys.Operations.ToNonlinearSys
import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialState
import CORALean.ContDynamics.NonlinDASys.Operations.SteadyState
import CORALean.ContDynamics.NonlinDASys.Operations.JointReachSet
import CORALean.ContDynamics.NonlinDASys.Operations.LinError
import CORALean.ContDynamics.NonlinDASys.Operations.LinErrorCora
import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinearCora

/-!
# What `NonlinDASys` computes

`ToNonlinearSys` eliminates the algebraic variable through a reduced model; `ReachUnion` runs
the reduced system's re-linearization loop.
-/
