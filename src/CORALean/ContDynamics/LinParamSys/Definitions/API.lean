module

public import CORALean.ContDynamics.LinParamSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.LinParamSys.Definitions.IsOrderAdmissibleFloat

/-!
# What `Reach (LinParamSys ℐ)` means

`ReachUnionExact` is what `Reach` asks of it, positional in the horizon and the
initial set: constant-parameter, at every matrix the sets `sys.A` and `sys.B` hold, under an
input set in input coordinates. `IsOrderAdmissibleFloat` is when a float order is sound.
-/
