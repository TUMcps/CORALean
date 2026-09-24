import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
import CORALean.ContDynamics.LinParamSysDT.Operations.ReachUnion
import CORALean.ContDynamics.LinParamSysDT.Operations.Simulate

/-!
# What `LinParamSysDT` computes

`Reach`, character for character `LinearSysDT.reach`'s recursion at a
set-valued matrix. `Simulate` samples one run at a matrix chosen per step.
`ReachUnion` packages `reach`'s steps as `Reach`'s `SetUnion`.
-/
