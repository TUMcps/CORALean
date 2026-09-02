import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
import CORALean.ContDynamics.NeurNetContrSysDT.Operations
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.API

/-!
# A neural network in the loop of a discrete-time plant, collected

The plant, the controller and what a run of the two is in `NeurNetContrSysDT`,
the alternating recursion in `Operations`, its guarantee in `Theorems`. No
`Instances`: an algorithm implements no class.

Everything here is composition. The controller's enclosure and the plant's step
were each proved without the other in view, and this directory adds a recursion
that calls them in turn.
-/
