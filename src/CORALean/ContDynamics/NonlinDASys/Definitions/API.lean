import CORALean.ContDynamics.NonlinDASys.Definitions.Index1
import CORALean.ContDynamics.NonlinDASys.Definitions.ReachUnionExact
import CORALean.ContDynamics.NonlinDASys.Definitions.ReducedModel
import CORALean.ContDynamics.NonlinDASys.Definitions.WithSteps
import CORALean.ContDynamics.NonlinDASys.Definitions.LinInclusion
import CORALean.ContDynamics.NonlinDASys.Definitions.LinPoint
import CORALean.ContDynamics.NonlinDASys.Definitions.LinPointCertifies
import CORALean.ContDynamics.NonlinDASys.Definitions.ErrorLoopResult
import CORALean.ContDynamics.NonlinDASys.Definitions.HessData
import CORALean.ContDynamics.NonlinDASys.Definitions.AbstractionError
import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptPass
import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptState
import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptTuning
import CORALean.ContDynamics.NonlinDASys.Definitions.FloatModel
import CORALean.ContDynamics.NonlinDASys.Definitions.CompositionalState

/-!
# What `NonlinDASys` means beyond the system itself

`Index1` is CORA's index-1 assumption, `∂g/∂y` invertible; `ReducedModel` is the algebraic
variable solved for, as data; `WithSteps` bundles the system, a reduced model and the
`NonlinearSys.WithSteps` data of the reduced system; `ReachUnionExact` is the reachable set
that run encloses. `FloatModel` is what a float run evaluates in place of `f` and `g`.
-/
