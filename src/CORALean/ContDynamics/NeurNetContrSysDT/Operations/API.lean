import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.ReachUnion
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate

/-!
# What `NeurNetContrSysDT` computes

`Reach`: the alternation of one plant step against the controller's enclosure
of its own input. `Simulate` samples one closed-loop run directly.
`ReachUnion` packages `reach`'s steps as `Reach`'s `SetUnion`.
-/
