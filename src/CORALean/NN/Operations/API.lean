import CORALean.NN.Operations.AtSchedule
import CORALean.NN.Operations.Convergent
import CORALean.NN.Operations.DifferentiableChain
import CORALean.NN.Operations.ExplainBox
import CORALean.NN.Operations.LayerSensitivity
import CORALean.NN.Operations.NetworkConvergent
import CORALean.NN.Operations.Enclose
import CORALean.NN.Operations.EncloseAt
import CORALean.NN.Operations.Raise
import CORALean.NN.Operations.Refine
import CORALean.NN.Operations.RefineLayer
import CORALean.NN.Operations.RefineLoop
import CORALean.NN.Operations.RefinementLipschitz
import CORALean.NN.Operations.RefinementNeuron
import CORALean.NN.Operations.RefinementRank
import CORALean.NN.Operations.RefineWorst
import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Operations.ToLayer
import CORALean.NN.Operations.VerifySplit
import CORALean.NN.Operations.WorstIndex

/-!
# What a network does, collected

`Enclose` is the pipeline itself; `ToLayer` is what makes a sub-network usable
as a layer, and so what makes the graph nest. `ExplainBox` is the input set a
sufficient-explanation query is asked over. `VerifySplit` recurses `Enclose`
over a checker and a splitter, budgeted by depth, taking no side on either.

`LayerSensitivity` and `Sensitivity` are the other direction: the Jacobian
backpropagated from the output, which is what a refinement heuristic weights a
neuron's approximation error by. Neither carries an obligation — no enclosure
depends on them — so `DifferentiableChain` is separate, the hypothesis under
which `Theorems.SensitivityFDeriv` identifies them with the derivative.

`NN.Schedule` is the refinement loop's state; `Raise`/`Refine`/`RefineLayer`/
`RefineLoop` build one, and `AtSchedule`/`EncloseAt` read one against a
network. `RefinementRank`/`WorstIndex`/`RefineWorst` pick the layer a
layer-wise step moves and `RefinementNeuron` the neuron a neuron-wise one does,
out of the sensitivity and the error — rankings with no obligation, again.
`Convergent`/`NetworkConvergent` are the other side, the hypotheses under which
spending orders actually shrinks the enclosure onto the exact image, and
`RefinementLipschitz` is the per-layer form of the bound those hypotheses ask of
every tail.
-/
