module

public import CORALean.ContDynamics.LinParamSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.LinParamSys.Definitions.WithInput
public import CORALean.ContDynamics.LinParamSys.Definitions.WithInputReachUnionExact
public import CORALean.ContDynamics.LinParamSys.Definitions.WithInputSplit
public import CORALean.ContDynamics.LinParamSys.Definitions.WithInputSplitReachUnionExact
public import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat

/-!
# What `Reach (LinParamSys ℐ)` means

`ReachUnionExact` is what `Reach` asks of it, positional in the horizon and the
initial set: homogeneous, constant-parameter, at every matrix the
set `sys.A` holds; `WithInput` and `WithInputReachUnionExact` the same with an
input set, `0 ∈ U` a field; `WithInputSplit` and its own `ReachUnionExact` drop
that field, the input set anywhere. `OrderAdmissibleFloat` is when a float order is sound.
-/
