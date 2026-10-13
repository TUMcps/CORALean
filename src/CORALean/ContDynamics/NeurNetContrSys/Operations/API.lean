module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachOrder
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnion
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloatChecked
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnionFloat

/-!
# What `NeurNetContrSys` computes

`Reach`, the two-rate recursion: the network's enclosure of the controller
closing every period, `LinearSys`'s own machinery taking the steps inside it.
`ReachOrder`/`ReachUnion` are `Instances`' Taylor order and `SetUnion`. `ReachFloat` is
`Reach` at float zonotopes, the plant sampled by `discretizeEnclosureFloat`.
-/
