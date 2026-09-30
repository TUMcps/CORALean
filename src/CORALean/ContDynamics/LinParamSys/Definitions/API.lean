import CORALean.ContDynamics.LinParamSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinParamSys.Definitions.WithInput
import CORALean.ContDynamics.LinParamSys.Definitions.WithInputReachUnionExact
import CORALean.ContDynamics.LinParamSys.Definitions.WithInputSplit
import CORALean.ContDynamics.LinParamSys.Definitions.WithInputSplitReachUnionExact

/-!
# What `Reach (LinParamSys ℐ)` means

`ReachUnionExact` is what `Reach` asks of it, positional in the horizon and the
initial set: homogeneous, constant-parameter, at every matrix the
set `sys.A` holds; `WithInput` and `WithInputReachUnionExact` the same with an
input set, `0 ∈ U` a field; `WithInputSplit` and its own `ReachUnionExact` drop
that field, the input set anywhere.
-/
