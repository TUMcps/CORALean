import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
import CORALean.ContDynamics.NeurNetContrSys.Operations
import CORALean.ContDynamics.NeurNetContrSys.Theorems.API

/-!
# A neural network in the loop of a continuous-time plant, collected

The plant, the controller and what a zero-order-hold run of the two is in
`NeurNetContrSys`, the two-rate recursion in `Operations`, its guarantee in
`Theorems`. No `Instances`: an algorithm implements no class.

The enclosure is the loose reading of a held input. A period is handed to
`LinearSys` as a set of admissible inputs, which admits every input that jitters
inside that set between samples; the constancy a zero-order hold provides buys
precision and is not used. `Theorems.Period` is where it is dropped and says so.
-/
