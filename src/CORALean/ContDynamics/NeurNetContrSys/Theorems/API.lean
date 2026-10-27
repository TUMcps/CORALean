module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.AugmentFlow
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.CartProdOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfCheckFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.JoinInputInj
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.MulVecJoinInput
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.OfFullIsTrajectoryIff
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ProjectOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatCheckedEqSome
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetExactOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachSetExactSubsetReach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionFloatOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachWithOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachWithTimePointOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatAugmentFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatLeftCols
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatRightCols

/-!
# What a sampled network in the loop guarantees

`ReachWithOuter`, at every plant, chains the control periods — each a run of the plant under
the held input, read through `ContDynamics.IsTrajectory` — for any reachability algorithm of the
extended state `[x; u]` that encloses those runs ([1, Alg. 2]); `ReachWithTimePointOuter` at the
period ends alone. At a linear plant `AugmentFlow` reads a period as a run of the augmented linear
system, the external inputs `U_ext` entering through `B_ext` (`JoinInputInj` returns them from the
plant's input vector, `MulVecJoinInput` splits `B` over its two parts, `ToRealMatLeftCols` and
`ToRealMatRightCols` read the split in the plant's scalar), `ReachOuter` is the result for `reach`,
`HoldsOfReach` says what checking a specification on it buys; `CartProdOuter`/`ProjectOuter`
are the product and projection it runs with.

`ReachSetExactOuter`/`ReachSetExactSubsetReach` restate `ReachOuter` on the reachable set
rather than on one run — every run is in it, and it, in turn, is inside `reach`.
`ReachOrderAdmissible`/`ReachUnionOuter` are `Instances`' guarantee, `ReachFloatOuter` `ReachOuter`
in floats, through `ToRealMatAugmentFloat`. `OfFullTrajectoryIff` is the loop with no external
input (`m = nrOfInputs`): the run of the plant under the network's output alone.

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/
