import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

/-!
# What a linearization computes

The two halves of one linearization: `Linearize` is the linear system, and
`LinInput` the set its input has to range over for the two to agree. Neither
mentions a derivative — what the split costs is an `AbstractionError`
certificate, not a bound on `f`.
-/
