module

public import CORALean.ContDynamics.NeurNetContrSysNL.NeurNetContrSysNL
public import CORALean.ContDynamics.NeurNetContrSysNL.Operations.API
public import CORALean.ContDynamics.NeurNetContrSysNL.Theorems.API

/-!
# A neural network in the loop of a nonlinear plant, collected

The plant, the controller and what a zero-order-hold run of the two is in `NeurNetContrSysNL`,
the loop over the control periods in `Operations`, its guarantee in `Theorems`. The reachability
algorithm for the extended system of one period, and the Cartesian product and projection of
sets, are arguments, as the paper's Alg. 2 leaves them: the guarantee holds for whichever the caller
supplies, given that each encloses.
-/
