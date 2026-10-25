module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Augment
public import CORALean.ContDynamics.NeurNetContrSys.Operations.AugmentFloat
public import CORALean.ContDynamics.NeurNetContrSys.Operations.CartProd
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Project
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloatChecked
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachOrder
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnion
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnionFloat
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachWith

/-!
# What `NeurNetContrSys` computes

`ReachWith`, [1, Alg. 2] at any plant: the network's image of the set reached so far, stacked
under it, reached as the extended state `[x; u]` of a control period by an algorithm the caller
supplies, and projected back. `Reach` is it at a linear plant, the period reached by
`LinearSys`'s own machinery on the `Augment`ed system, the external inputs `U_ext` entering through
its input matrix, the product and projection `CartProd`
and `Project`; `ReachFloat` is `Reach` at float zonotopes, on `AugmentFloat`.
`ReachOrder`/`ReachUnion` are `Instances`' Taylor order and `SetUnion`. `Basic` holds the plant's
input `[a; e]` (`input`, built by `joinInput`), the split of an input matrix (`leftCols`,
`rightCols`) and the loop in which the network drives every input (`ofFull`).

## References

* [1] N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715, 2022.
-/
