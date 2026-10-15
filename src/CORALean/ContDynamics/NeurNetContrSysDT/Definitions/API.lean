module

public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.Linear
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.InputSet
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.IsTrajectory
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachOptions
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachSet
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachUnionExact

/-!
# What `NeurNetContrSysDT` means

`InputSet` is the plant's input set `U_nn × U_ext` and `IsTrajectory` a run of the loop.

`ReachSet`: every state some run reaches after `k` steps, at any plant, quantified over the
runs themselves — the exact set, not an enclosure of it. `ReachUnionExact` is
what `Reach` asks of it, run at the controller's own
`eval` in place of a free, `Sound`-constrained input; `Linear` is the loop at a linear plant
as the family `Reach` is instantiated at.
-/
