module

public import CORALean.ContDynamics.LinParamSysDT.Operations.Canonical
public import CORALean.ContDynamics.LinParamSysDT.Operations.InputSet
public import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
public import CORALean.ContDynamics.LinParamSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.LinParamSysDT.Operations.Simulate
public import CORALean.ContDynamics.LinParamSysDT.Operations.ToLinParam

/-!
# What `LinParamSysDT` computes

`Reach`, character for character `LinearSysDT.reach`'s recursion at a
set-valued matrix. `Simulate` samples one run at a matrix chosen per step.
`ReachUnion` packages `reach`'s steps as `Reach`'s `SetUnion`.
-/
