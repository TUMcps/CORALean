import CORALean.NN.Theorems.ActivationLipschitz
import CORALean.NN.Theorems.AtScheduleEval
import CORALean.NN.Theorems.EvalDifferentiable
import CORALean.NN.Theorems.EvalLipschitz
import CORALean.NN.Theorems.LinearConvergent
import CORALean.NN.Theorems.LinearExact
import CORALean.NN.Theorems.LinearLipschitz
import CORALean.NN.Theorems.LinearWithErrorZero
import CORALean.NN.Theorems.MergeErrorSplit
import CORALean.NN.Theorems.MinSuffExplanation
import CORALean.NN.Theorems.MultiLayerRefinementConverges
import CORALean.NN.Theorems.NeuronMergingNetworkOuter
import CORALean.NN.Theorems.NeuronMergingOuter
import CORALean.NN.Theorems.PropagateAtInflate
import CORALean.NN.Theorems.PropagateAtOuter
import CORALean.NN.Theorems.PropagateOuter
import CORALean.NN.Theorems.ReluNotDifferentiable
import CORALean.NN.Theorems.Robustness
import CORALean.NN.Theorems.SensitivityActivation
import CORALean.NN.Theorems.SensitivityFDeriv
import CORALean.NN.Theorems.SensitivityLinear
import CORALean.NN.Theorems.SensitivityOfMatrix
import CORALean.NN.Theorems.SensitivitySigmoid
import CORALean.NN.Theorems.SensitivityTanh
import CORALean.NN.Theorems.SigmoidLipschitz
import CORALean.NN.Theorems.SigmoidRefinementConverges
import CORALean.NN.Theorems.SuffExplanation
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationConverseFails
import CORALean.NN.Theorems.SuffExplanationTransfer
import CORALean.NN.Theorems.Verified

/-!
# What a network's enclosure guarantees, collected

`PropagateOuter` is the induction over the graph, `Verified` what it buys when a
specification is checked on the result, and `Robustness` the one a classifier is
usually checked against, with the bounds that discharge it.

`LinearWithErrorZero`, `NeuronMergingOuter`, `NeuronMergingNetworkOuter` and
`MergeErrorSplit` are the sound network reduction by neuron merging [1]: a plain
linear layer as its error-free case, the single-bucket containment at every
bucket and any layer of any network, and disjoint buckets by Minkowski sum.

`SuffExplanation`, `MinSuffExplanation` and `SuffExplanationAbstract` are provable local
explanations [2]; `SuffExplanationTransfer` carries sufficiency from an abstract network to the
original, and `SuffExplanationConverseFails` is why that carrying is one-directional.

`SensitivityFDeriv` is what the refinement heuristic rests on [3]: with `EvalDifferentiable`,
the chain rule identifies the backpropagated Jacobian with `fderiv` wherever every layer has
one. `SensitivityOfMatrix` hands that to `SensitivityLinear` and `SensitivityActivation`, and
`ReluNotDifferentiable` is why ReLU gets none. `AtScheduleEval`, `PropagateAtOuter` and
`PropagateAtInflate` are the loop it drives; its hypothesis is discharged at one activation by
`SigmoidRefinementConverges` and at a three-layer chain by `MultiLayerRefinementConverges`, out
of `LinearExact`, `LinearConvergent`, `LinearLipschitz`, `ActivationLipschitz`,
`SigmoidLipschitz` and `EvalLipschitz`.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
* [2] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [3] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/
