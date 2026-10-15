module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.InputSet
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.IsTrajectory
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachOptions
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSet
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.Linear

/-!
# What `NeurNetContrSys` means

`InputSet` is the plant's input set `U_nn × U_ext` and `IsTrajectory` the run of the loop over its
control periods. `ReachSet`: every state some zero-order-hold run reaches, quantified over the
runs themselves — the exact set, not an enclosure of it. `Linear` is
the system with its external input set, as the family `Reach` is instantiated at, and
`ReachUnionExact` what
`Reach` asks of it, at the controller's own `eval`;
`ReachOptions` is CORA's `options` for `NeurNetContrSys.reach`.
-/
