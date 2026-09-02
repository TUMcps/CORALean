import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSys.Theorems.Period
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter

/-!
# What a sampled network in the loop guarantees

`Period` is the join — one control period read as a linear run under the
propagated input set, and the only place `NN` and `LinearSys` meet. `ReachOuter`
chains it over the periods, `HoldsOfReach` says what checking a specification on
the result buys.
-/
