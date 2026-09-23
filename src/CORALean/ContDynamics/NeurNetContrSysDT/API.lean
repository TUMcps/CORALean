import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.API
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.API
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.API
import CORALean.ContDynamics.NeurNetContrSysDT.Cost.API

/-!
# A neural network in the loop of a discrete-time plant, collected

The plant, the controller and what a run of the two is in `NeurNetContrSysDT`,
the alternating recursion in `Operations`, the set a run reaches in `ReachSet`,
its guarantee in `Theorems`, its cost in `Cost`. No `Instances`: an algorithm
implements no class.

Everything here is composition. The controller's enclosure and the plant's step
were each proved without the other in view, and this directory adds a recursion
that calls them in turn.
-/
