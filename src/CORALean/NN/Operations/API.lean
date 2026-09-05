import CORALean.NN.Operations.DifferentiableChain
import CORALean.NN.Operations.ExplainBox
import CORALean.NN.Operations.LayerSensitivity
import CORALean.NN.Operations.Propagate
import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Operations.ToLayer

/-!
# What a network does, collected

`Propagate` is the pipeline itself; `ToLayer` is what makes a sub-network usable
as a layer, and so what makes the graph nest. `ExplainBox` is the input set a
sufficient-explanation query is asked over.

`LayerSensitivity` and `Sensitivity` are the other direction: the Jacobian
backpropagated from the output, which is what a refinement heuristic weights a
neuron's approximation error by. Neither carries an obligation — no enclosure
depends on them — so `DifferentiableChain` is separate, the hypothesis under
which `Theorems.SensitivityFDeriv` identifies them with the derivative.
-/
