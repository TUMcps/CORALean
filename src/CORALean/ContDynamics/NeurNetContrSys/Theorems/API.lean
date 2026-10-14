module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.CartProdOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ExtendedFEqAugment
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfCheckFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.Period
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ProjectOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatCheckedEqSome
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetSubsetReach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionFloatOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachWithOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachWithTimePointOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatAugmentFloat

/-!
# What a sampled network in the loop guarantees

`Period` is the join, at every plant — one control period read as a run of the extended system,
and the only place `NN` and the plant meet. `ReachWithOuter` chains it over the periods for any
reachability algorithm of the extended system that encloses ([1, Alg. 2]),
`ReachWithTimePointOuter` at the period ends alone. At a linear plant `ExtendedFEqAugment` reads
the extended system as the augmented linear one, `ReachOuter` is the result for `reach`,
`HoldsOfReach` says what checking a specification on it buys; `CartProdOuter`/`ProjectOuter`
are the product and projection it runs with.

`ReachSetOuter`/`ReachSetSubsetReach` restate `ReachOuter` on the reachable set
rather than on one run — every run is in it, and it, in turn, is inside `reach`.
`ReachOrderAdmissible`/`ReachUnionOuter` are `Instances`' guarantee, `ReachFloatOuter` `ReachOuter`
in floats, through `ToRealMatAugmentFloat`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/
