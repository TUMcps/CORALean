import CORALean.ContDynamics.NonlinDASys.Definitions.API
import CORALean.ContDynamics.NonlinDASys.Instances
import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContDynamics.NonlinDASys.Operations.API
import CORALean.ContDynamics.NonlinDASys.Theorems.API

/-!
# Nonlinear differential-algebraic systems, collected

The system and its trajectories in `NonlinDASys`; the index-1 assumption, the reduced model
and the reachable set in `Definitions`; the local reduction an index-1 system admits, the
correspondence of trajectories with the reduced ordinary system and the outer guarantee in
`Theorems`. Reachability is through that reduced system, which needs the reduced model as
data: not CORA's algorithm, which linearizes the differential-algebraic system with an
error term for the algebraic variable.
-/
