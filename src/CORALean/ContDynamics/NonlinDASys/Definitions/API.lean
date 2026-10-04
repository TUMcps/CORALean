import CORALean.ContDynamics.NonlinDASys.Definitions.Index1
import CORALean.ContDynamics.NonlinDASys.Definitions.ReachUnionExact
import CORALean.ContDynamics.NonlinDASys.Definitions.ReducedModel
import CORALean.ContDynamics.NonlinDASys.Definitions.WithSteps
import CORALean.ContDynamics.NonlinDASys.Definitions.LinInclusion

/-!
# What `NonlinDASys` means beyond the system itself

`Index1` is CORA's index-1 assumption, `∂g/∂y` invertible; `ReducedModel` is the algebraic
variable solved for, as data; `WithSteps` bundles the system, a reduced model and the
`NonlinearSys.WithSteps` data of the reduced system; `ReachUnionExact` is the reachable set
that run encloses.
-/
