import CORALean.ContDynamics.LinParamSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinParamSys.Definitions.WithInput
import CORALean.ContDynamics.LinParamSys.Definitions.WithInputReachUnionExact

/-!
# What `Reach (LinParamSys ℐ)` means

`ReachUnionExact` is what `Reach` asks of it, at the point case's
`LinearSys.ReachParams`: homogeneous, constant-parameter, at every matrix the
set `sys.A` holds; `WithInput` and `WithInputReachUnionExact` the same with an
input set.
-/
