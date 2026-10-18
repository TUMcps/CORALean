module

public import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachOptions
public import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.LinParamSysDT.Instances
public import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
public import CORALean.ContDynamics.LinParamSysDT.Operations.API
public import CORALean.ContDynamics.LinParamSysDT.Theorems.API

/-!
# Discrete-time linear systems with a set-valued system matrix, collected

The system and what it denotes in `LinParamSysDT`, reachability in
`Operations`, its guarantee in `Theorems`.

`ReachSetExact` is the set reachable in `k` steps at every matrix the set holds,
`ReachUnionExact` the one `Reach` asks to be enclosed, every step up to the
horizon, and `Instances` is the instance itself.
-/
