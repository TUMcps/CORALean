import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachParams
import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSet
import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachUnionExact

/-!
# What `NeurNetContrSys` means

`ReachSet`: every state some zero-order-hold run reaches, quantified over the
runs themselves — the exact set, not an enclosure of it. `ReachParams`/
`ReachUnionExact` are what `Reach` asks of it, at the controller's own `eval`.
-/
