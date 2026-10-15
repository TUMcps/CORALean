module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Basic
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.OutputSet
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.SimulateBoxFloat

/-!
# What `NeurNetContrSysDT` computes

`Reach`: the alternation of one plant step against the controller's enclosure
of its own input. `Simulate` samples one closed-loop run directly.
`ReachUnion` packages `reach`'s steps as `Reach`'s `SetUnion`. `Map` is one step of the loop
at a linear plant, the function a run with no disturbance iterates; `OutputSet` encloses the
outputs of the loop at a state set, the network's and the external inputs entering separately.
`Basic` holds the plant's input `[a; e]` (`input`) and the loop in which the network
drives every input (`ofFull`).
-/
