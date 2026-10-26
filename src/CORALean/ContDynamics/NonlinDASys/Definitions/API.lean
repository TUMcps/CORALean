module

public import CORALean.ContDynamics.NonlinDASys.Definitions.IsIndex1
public import CORALean.ContDynamics.NonlinDASys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinDASys.Definitions.ReducedModel
public import CORALean.ContDynamics.NonlinDASys.Definitions.WithSteps
public import CORALean.ContDynamics.NonlinDASys.Definitions.LinInclusion
public import CORALean.ContDynamics.NonlinDASys.Definitions.LinPoint
public import CORALean.ContDynamics.NonlinDASys.Definitions.LinPointCertifies
public import CORALean.ContDynamics.NonlinDASys.Definitions.ErrorLoopResult
public import CORALean.ContDynamics.NonlinDASys.Definitions.HessData
public import CORALean.ContDynamics.NonlinDASys.Definitions.AbstractionError
public import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptPass
public import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptState
public import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptTuning
public import CORALean.ContDynamics.NonlinDASys.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinDASys.Definitions.CompositionalState
public import CORALean.ContDynamics.NonlinDASys.Definitions.OutputFloatModel

/-!
# What `NonlinDASys` means beyond the system itself

`IsIndex1` is CORA's index-1 assumption, `∂g/∂y` invertible; `ReducedModel` is the algebraic
variable solved for, as data; `WithSteps` bundles the system, a reduced model and the
`NonlinearSys.WithSteps` data of the reduced system; `ReachUnionExact` is the reachable set
that run encloses. `FloatModel` is what a float run evaluates in place of `f` and `g`.
-/
