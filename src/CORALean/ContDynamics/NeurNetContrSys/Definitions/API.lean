import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachOptions
import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSet
import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.NeurNetContrSys.Definitions.WithPeriod

/-!
# What `NeurNetContrSys` means

`ReachSet`: every state some zero-order-hold run reaches, quantified over the
runs themselves — the exact set, not an enclosure of it. `WithPeriod` is
the system with its control period, CORA's `sys.dt`, and `ReachUnionExact` what
`Reach` asks of it, at the controller's own `eval`;
`ReachOptions` is CORA's `options` for `NeurNetContrSys.reach`.
-/
