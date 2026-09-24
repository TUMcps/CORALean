import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachParams
import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachSet
import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachUnionExact

/-!
# What `NeurNetContrSysDT` means

`ReachSet`: every state some run reaches after `k` steps, quantified over the
runs themselves — the exact set, not an enclosure of it. `ReachParams` and
`ReachUnionExact` are what `Reach` asks of it, run at the controller's own
`eval` in place of a free, `Sound`-constrained input.
-/
