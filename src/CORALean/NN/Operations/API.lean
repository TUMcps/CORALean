import CORALean.NN.Operations.DifferentiableChain
import CORALean.NN.Operations.ExplainBox
import CORALean.NN.Operations.LayerSensitivity
import CORALean.NN.Operations.Propagate
import CORALean.NN.Operations.RefinementConvergent
import CORALean.NN.Operations.RefinementLipschitz
import CORALean.NN.Operations.RefinementNeuron
import CORALean.NN.Operations.RefinementRank
import CORALean.NN.Operations.Schedule
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

`Schedule` is the refinement loop: an order pattern per layer, the network it
names, and one step. `RefinementRank` picks the layer a layer-wise step moves
and `RefinementNeuron` the neuron a neuron-wise one does, out of the sensitivity
and the error — rankings with no obligation, again. `RefinementConvergent` is
the other side, the hypotheses under which spending orders actually shrinks the
enclosure onto the exact output set, and `RefinementLipschitz` is the per-layer
form of the bound those hypotheses ask of every tail.
-/
