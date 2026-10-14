module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.API
public import CORALean.ContDynamics.NeurNetContrSys.Instances
public import CORALean.ContDynamics.NeurNetContrSys.Operations.API
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.API

/-!
# A neural network in the loop of a plant, collected

CORA's one `neurNetContrSys` over every plant: the plant interface, the controller and what a
zero-order-hold run of the two is in `NeurNetContrSys`, [1, Alg. 2] over the control periods in
`Operations` (`reachWith` at any plant, `reach` at a linear one), the set a run reaches in
`ReachSet`, its guarantee in `Theorems`, and `Instances`, the linear loop's `Reach`: one period
boundary per branch, at a derived Taylor order.

The input is held exactly: a period is reached as one state of the extended system `[x; u]`
with `u̇ = 0`, so the same input acts over the whole period. The dependence of the network's
output on the state at the period's start is not kept, the product of the two being the plain
one (`cartProd`).

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/
