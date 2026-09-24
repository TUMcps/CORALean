import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachParams
import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachSetOfInit
import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinParamSysDT.Definitions.WithInput
import CORALean.ContDynamics.LinParamSysDT.Instances
import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
import CORALean.ContDynamics.LinParamSysDT.Operations.API
import CORALean.ContDynamics.LinParamSysDT.Theorems.API

/-!
# Discrete-time linear systems with a set-valued system matrix, collected

The system and what it denotes in `LinParamSysDT`, reachability in
`Operations`, its guarantee in `Theorems`.

`WithInput` pairs a system with the input set `Reach.Params` cannot hold;
`ReachParams`, `ReachSetOfInit` and `ReachUnionExact` are what `Reach` needs
beyond that, and `Instances` is the instance itself.
-/
