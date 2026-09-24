import CORALean.ContDynamics.NeurNetContrSys.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachOrder
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnion

/-!
# What `NeurNetContrSys` computes

`Reach`, the two-rate recursion: the network's enclosure of the controller
closing every period, `LinearSys`'s own machinery taking the steps inside it.
`ReachOrder`/`ReachUnion` are `Instances`' Taylor order and `SetUnion`.
-/
