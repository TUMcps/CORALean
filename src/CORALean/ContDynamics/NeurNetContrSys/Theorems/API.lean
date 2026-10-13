module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.Period
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetSubsetReach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionFloatOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatCheckedEqSome
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfCheckFloat

/-!
# What a sampled network in the loop guarantees

`Period` is the join — one control period read as a linear run under the
enclosed input set, and the only place `NN` and `LinearSys` meet. `ReachOuter`
chains it over the periods, `HoldsOfReach` says what checking a specification on
the result buys.

`ReachSetOuter`/`ReachSetSubsetReach` restate `ReachOuter` on the reachable set
rather than on one run — every run is in it, and it, in turn, is inside `reach`.
`ReachOrderAdmissible`/`ReachUnionOuter` are `Instances`' guarantee, `ReachFloatOuter` `ReachOuter`
in floats.
-/
