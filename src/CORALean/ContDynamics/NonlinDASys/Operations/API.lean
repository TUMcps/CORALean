import CORALean.ContDynamics.NonlinDASys.Operations.ReachUnion
import CORALean.ContDynamics.NonlinDASys.Operations.ToNonlinearSys
import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialState
import CORALean.ContDynamics.NonlinDASys.Operations.SteadyState

/-!
# What `NonlinDASys` computes

`ToNonlinearSys` eliminates the algebraic variable through a reduced model; `ReachUnion` runs
the reduced system's re-linearization loop.
-/
