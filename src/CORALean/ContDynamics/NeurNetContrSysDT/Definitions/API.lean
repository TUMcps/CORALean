module

public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachOptions
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachSet
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachUnionExact

/-!
# What `NeurNetContrSysDT` means

`ReachSet`: every state some run reaches after `k` steps, quantified over the
runs themselves — the exact set, not an enclosure of it. `ReachUnionExact` is
what `Reach` asks of it, run at the controller's own
`eval` in place of a free, `Sound`-constrained input.
-/
