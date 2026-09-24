import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfCheck
import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSys.Theorems.Period
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetOuter
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetSubsetReach

/-!
# What a sampled network in the loop guarantees

`Period` is the join — one control period read as a linear run under the
enclosed input set, and the only place `NN` and `LinearSys` meet. `ReachOuter`
chains it over the periods, `HoldsOfReach` says what checking a specification on
the result buys.

`ReachSetOuter`/`ReachSetSubsetReach` restate `ReachOuter` on the reachable set
rather than on one run — every run is in it, and it, in turn, is inside `reach`.
-/
