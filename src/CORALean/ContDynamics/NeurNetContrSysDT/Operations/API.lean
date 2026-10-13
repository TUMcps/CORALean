module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.SimulateBoxFloat

/-!
# What `NeurNetContrSysDT` computes

`Reach`: the alternation of one plant step against the controller's enclosure
of its own input. `Simulate` samples one closed-loop run directly.
`ReachUnion` packages `reach`'s steps as `Reach`'s `SetUnion`.
-/
