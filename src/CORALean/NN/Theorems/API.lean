import CORALean.NN.Theorems.ActivationLipschitz
import CORALean.NN.Theorems.AtScheduleEval
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.DisjointMisclassifiedOfBounds
import CORALean.NN.Theorems.EvalDifferentiable
import CORALean.NN.Theorems.EvalLipschitz
import CORALean.NN.Theorems.LinearConvergent
import CORALean.NN.Theorems.LinearExact
import CORALean.NN.Theorems.LinearLipschitz
import CORALean.NN.Theorems.LinearWithErrorZero
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.MemSafeSet
import CORALean.NN.Theorems.MergeErrorSplit
import CORALean.NN.Theorems.MinSuffExplanation
import CORALean.NN.Theorems.MinSuffExplanationAbstract
import CORALean.NN.Theorems.MinSuffExplanationCounterexample
import CORALean.NN.Theorems.MinSuffExplanationTransfer
import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.MultiLayerRefinementConverges
import CORALean.NN.Theorems.NeuronMergingNetworkOuter
import CORALean.NN.Theorems.NeuronMergingOuter
import CORALean.NN.Theorems.NotMemUnsafeSet
import CORALean.NN.Theorems.OutputSetSubset
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
import CORALean.NN.Theorems.SuffExplanationRefined
import CORALean.NN.Theorems.SuffExplanationTransfer
import CORALean.NN.Theorems.Verified

/-!
# What a network's enclosure guarantees, collected

`PropagateOuter` is the induction over the graph and `OutputSetSubset` its pointwise form;
`Verified` composes that with `Specification.holds_of_outer`, and `MemSafeSet`/`NotMemUnsafeSet`
read it directly against a safe or unsafe set. `Robustness` is the usual classifier requirement,
out of `Misclassified`, `MarginDir`, `DisjointMisclassifiedOfBounds` and `Classifies`.

`LinearWithErrorZero`, `NeuronMergingOuter`, `NeuronMergingNetworkOuter` and `MergeErrorSplit` are
the sound network reduction by neuron merging [1]: a plain linear layer as its error-free case,
single-bucket containment at every bucket and any layer, and disjoint buckets by Minkowski sum.

`SuffExplanation`, `MinSuffExplanation` and their `Abstract` forms are local explanations [2].
`SuffExplanationTransfer` carries sufficiency to the original network, discharged at a merged one;
`SuffExplanationRefined` and `MinSuffExplanationTransfer` carry it and minimality along a
refinement, `MinSuffExplanationCounterexample` certifies minimality, and
`SuffExplanationConverseFails` is why it goes one way.

`SensitivityFDeriv` is what the refinement heuristic [3] rests on: the backpropagated Jacobian
identified with `fderiv` wherever `EvalDifferentiable` holds, which `SensitivityOfMatrix` hands to
`SensitivityLinear`/`SensitivityActivation`; `ReluNotDifferentiable` is why ReLU gets none.
`AtScheduleEval`, `PropagateAtOuter` and `PropagateAtInflate` are the refinement loop, whose
hypothesis `SigmoidRefinementConverges` discharges at one activation and
`MultiLayerRefinementConverges` at a chain, out of the `Linear` and `Lipschitz` lemmas here.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
* [2] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [3] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/
