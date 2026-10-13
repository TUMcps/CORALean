module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.API
public import CORALean.ContDynamics.NeurNetContrSys.Instances
public import CORALean.ContDynamics.NeurNetContrSys.Operations.API
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.API

/-!
# A neural network in the loop of a continuous-time plant, collected

The plant, the controller and what a zero-order-hold run of the two is in
`NeurNetContrSys`, the two-rate recursion in `Operations`, the set a run
reaches in `ReachSet`, its guarantee in `Theorems`, and `Instances`, its
`Reach`: one homogeneous-plant period per branch, at a derived Taylor order.

The enclosure is the loose reading of a held input. A period is handed to
`LinearSys` as a set of admissible inputs, which admits every input that jitters
inside that set between samples; the constancy a zero-order hold provides buys
precision and is not used. `Theorems.Period` is where it is dropped and says so.
-/
