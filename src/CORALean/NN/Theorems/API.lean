import CORALean.NN.Theorems.ActivationLipschitz
import CORALean.NN.Theorems.AtScheduleEval
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.DisjointMisclassifiedOfBounds
import CORALean.NN.Theorems.EvalDifferentiable
import CORALean.NN.Theorems.EvalLipschitz
import CORALean.NN.Theorems.ExistsMergeBucketAll
import CORALean.NN.Theorems.LinearConvergent
import CORALean.NN.Theorems.LinearExact
import CORALean.NN.Theorems.LinearLipschitz
import CORALean.NN.Theorems.LinearWithErrorZero
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.MemSafeSet
import CORALean.NN.Theorems.MergeBucketCardMono
import CORALean.NN.Theorems.MergeBucketMono
import CORALean.NN.Theorems.MergeErrorSplit
import CORALean.NN.Theorems.MergeErrorWidthLe
import CORALean.NN.Theorems.MergeErrorWidthLeRow
import CORALean.NN.Theorems.MinSuffExplanation
import CORALean.NN.Theorems.MinSuffExplanationAbstract
import CORALean.NN.Theorems.MinSuffExplanationCounterexample
import CORALean.NN.Theorems.MinSuffExplanationAbstractOfMin
import CORALean.NN.Theorems.MinSuffExplanationAbstractOfRefined
import CORALean.NN.Theorems.MinSuffExplanationExact
import CORALean.NN.Theorems.MinSuffExplanationExactOfRefined
import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.MultiLayerRefinementConverges
import CORALean.NN.Theorems.ExistsMergeTolerance
import CORALean.NN.Theorems.ExistsScheduleSigmoidLinearSigmoidSubset
import CORALean.NN.Theorems.NeuronMergingNetworkOuter
import CORALean.NN.Theorems.NeuronMergingOuter
import CORALean.NN.Theorems.NotMemUnsafeSet
import CORALean.NN.Theorems.ImageSubset
import CORALean.NN.Theorems.EncloseAtInflate
import CORALean.NN.Theorems.EncloseAtOuter
import CORALean.NN.Theorems.ImageSubsetEncloseAt
import CORALean.NN.Theorems.EncloseNotMonotone
import CORALean.NN.Theorems.ReducesAtOuter
import CORALean.NN.Theorems.ReducesAtRefl
import CORALean.NN.Theorems.HoldsOfReducesAt
import CORALean.NN.Theorems.ImageSubsetRefine
import CORALean.NN.Theorems.ImageSubsetRefineLayer
import CORALean.NN.Theorems.ImageSubsetRefineLoop
import CORALean.NN.Theorems.EncloseOuter
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
import CORALean.NN.Theorems.ExistsScheduleSigmoidSubset
import CORALean.NN.Theorems.SuffExplanation
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationConverseFails
import CORALean.NN.Theorems.SuffExplanationExact
import CORALean.NN.Theorems.SuffExplanationExactOfRefined
import CORALean.NN.Theorems.SuffExplanationExactOfReducesAt
import CORALean.NN.Theorems.SuffExplanationOfExact
import CORALean.NN.Theorems.SuffExplanationRefined
import CORALean.NN.Theorems.SuffExplanationTransfer
import CORALean.NN.Theorems.SuffExplanationOfNeuronMerging
import CORALean.NN.Theorems.SuffExplanationOfEnclose
import CORALean.NN.Theorems.HoldsOfEnclose
import CORALean.NN.Theorems.HoldsAllOfEnclose
import CORALean.NN.Theorems.HoldsOfSplit
import CORALean.NN.Theorems.VerifySplitSound

/-!
# What a network's enclosure guarantees, collected

`EncloseOuter`/`ImageSubset` are the graph induction, its pointwise form; `Verified` composes
`Specification.holds_of_outer`, read by `MemSafeSet`/`NotMemUnsafeSet` against a safe or unsafe set.
`Robustness` builds on `Misclassified`, `MarginDir`, `DisjointMisclassifiedOfBounds`, `Classifies`.
`HoldsOfSplit`/`VerifySplitSound` make verification complete: split once, or recurse to a depth.

`LinearWithErrorZero`, `NeuronMergingOuter`, `NeuronMergingNetworkOuter`, `MergeErrorSplit`,
`MergeErrorWidthLe`, `MergeErrorWidthLeRow` are neuron merging [1]: error-free linear layers,
bucket containment, the Minkowski split, tolerated by `ExistsMergeTolerance`'s `δ`-linear cost;
`MergeBucketMono`/`MergeBucketCardMono`/`ExistsMergeBucketAll` grow it; `EncloseNotMonotone`
forces `Reduction`'s `ReducesAt` into one induction — `HoldsOfReducesAt` is [1, Thm. 1].

`SuffExplanation`, `MinSuffExplanation` and their `Abstract` and `Exact` forms are local
explanations [2]. `SuffExplanationTransfer`/`OfExact` carry sufficiency to the original network,
`SuffExplanationRefined` and `MinSuffExplanationAbstractOfMin`/`OfRefined` carry it enclosure to
enclosure; the `ExactOfRefined` pair with `SuffExplanationExactOfReducesAt` is [2, Prop. 3] and
its discharge, `MinSuffExplanationCounterexample` and `SuffExplanationConverseFails` its limits.
`SensitivityFDeriv` is what the refinement heuristic [3] rests on: the backpropagated Jacobian
identified with `fderiv` wherever `EvalDifferentiable` holds, which `SensitivityOfMatrix` hands
to `SensitivityLinear`/`SensitivityActivation`; `ReluNotDifferentiable` is why ReLU gets none.
`AtScheduleEval`/`EncloseAtOuter`/`EncloseAtInflate` are the refinement loop: hypothesis
`SigmoidRefinementConverges` discharges one activation, `MultiLayerRefinementConverges` a chain.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
* [2] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [3] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/
