import CORALean.NN.Theorems.ActivationLipschitz
import CORALean.NN.Theorems.AtScheduleEval
import CORALean.NN.Theorems.BucketToleranceApprox
import CORALean.NN.Theorems.ChainEvalCons
import CORALean.NN.Theorems.ChainEvalNil
import CORALean.NN.Theorems.Classifies
import CORALean.NN.Theorems.CompressionPreprocessingOuter
import CORALean.NN.Theorems.DisjointMisclassifiedOfBounds
import CORALean.NN.Theorems.EncloseAtInflate
import CORALean.NN.Theorems.EncloseAtOuter
import CORALean.NN.Theorems.EncloseNotMonotone
import CORALean.NN.Theorems.EncloseOuter
import CORALean.NN.Theorems.EncloseOuterEval
import CORALean.NN.Theorems.EvalDifferentiable
import CORALean.NN.Theorems.EvalLipschitz
import CORALean.NN.Theorems.ExistsMergeBucketAll
import CORALean.NN.Theorems.ExistsMergeTolerance
import CORALean.NN.Theorems.ExistsScheduleLinearSigmoidSubset
import CORALean.NN.Theorems.ExistsScheduleSigmoidLinearSigmoidSubset
import CORALean.NN.Theorems.ExistsScheduleSigmoidSubset
import CORALean.NN.Theorems.ExplanationRefineLoopIff
import CORALean.NN.Theorems.GreedyAbstractExplanationEqGreedyMinimalExplanation
import CORALean.NN.Theorems.HoldsAllOfEnclose
import CORALean.NN.Theorems.HoldsOfCheck
import CORALean.NN.Theorems.HoldsOfEnclose
import CORALean.NN.Theorems.HoldsOfReduceOnTheFly
import CORALean.NN.Theorems.HoldsOfReducesAt
import CORALean.NN.Theorems.HoldsOfReducesAtSubset
import CORALean.NN.Theorems.HoldsOfSplit
import CORALean.NN.Theorems.ImageSubset
import CORALean.NN.Theorems.ImageSubsetEncloseAt
import CORALean.NN.Theorems.ImageSubsetRefine
import CORALean.NN.Theorems.ImageSubsetRefineLayer
import CORALean.NN.Theorems.ImageSubsetRefineLoop
import CORALean.NN.Theorems.IntervalChainBackpropAdjoint
import CORALean.NN.Theorems.IntervalChainFwdHasDerivAt
import CORALean.NN.Theorems.IsMinSuffExplanationGreedyAbstractExplanation
import CORALean.NN.Theorems.IsMinSuffExplanationGreedyMinimalExplanation
import CORALean.NN.Theorems.LinearLipschitz
import CORALean.NN.Theorems.LinearSigmoidConverges
import CORALean.NN.Theorems.MarginDir
import CORALean.NN.Theorems.MemSafeSet
import CORALean.NN.Theorems.MergeBucketCardMono
import CORALean.NN.Theorems.MergeBucketMono
import CORALean.NN.Theorems.MergeErrorSplit
import CORALean.NN.Theorems.MergeErrorWidthLe
import CORALean.NN.Theorems.MergeErrorWidthLeRow
import CORALean.NN.Theorems.MinSuffExplanation
import CORALean.NN.Theorems.MinSuffExplanationAbstract
import CORALean.NN.Theorems.MinSuffExplanationAbstractOfMin
import CORALean.NN.Theorems.MinSuffExplanationAbstractOfRefined
import CORALean.NN.Theorems.MinSuffExplanationCounterexample
import CORALean.NN.Theorems.MinSuffExplanationExact
import CORALean.NN.Theorems.MinSuffExplanationExactOfRefined
import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.MultiLayerRefinementConverges
import CORALean.NN.Theorems.NeuronMergingNetworkOuter
import CORALean.NN.Theorems.NeuronMergingOuter
import CORALean.NN.Theorems.NotMemUnsafeSet
import CORALean.NN.Theorems.Real.API
import CORALean.NN.Theorems.ReduceOnTheFlyOuter
import CORALean.NN.Theorems.ReducesAtCongr
import CORALean.NN.Theorems.ReducesAtOuter
import CORALean.NN.Theorems.ReducesAtRefl
import CORALean.NN.Theorems.RefinableLayerAtPatternSound
import CORALean.NN.Theorems.ReluNotDifferentiable
import CORALean.NN.Theorems.Robustness
import CORALean.NN.Theorems.ScheduleHeadCons
import CORALean.NN.Theorems.BackpropEqFDerivTranspose
import CORALean.NN.Theorems.BackpropEqTranspose
import CORALean.NN.Theorems.FgsmAttackDistLe
import CORALean.NN.Theorems.PgdAttackMemBox
import CORALean.NN.Theorems.SensitivityActivation
import CORALean.NN.Theorems.SensitivityFDeriv
import CORALean.NN.Theorems.SensitivityLinear
import CORALean.NN.Theorems.SensitivityOfMatrix
import CORALean.NN.Theorems.SensitivitySigmoid
import CORALean.NN.Theorems.SensitivityTanh
import CORALean.NN.Theorems.SigmoidLipschitz
import CORALean.NN.Theorems.SigmoidRefinementConverges
import CORALean.NN.Theorems.SoundEval
import CORALean.NN.Theorems.SoundHoldsAllOfEnclose
import CORALean.NN.Theorems.SoundHoldsOfEnclose
import CORALean.NN.Theorems.SoundVerifySplitSound
import CORALean.NN.Theorems.SoundVerifySplitWithSound
import CORALean.NN.Theorems.SuffExplanation
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanationConverseFails
import CORALean.NN.Theorems.SuffExplanationExact
import CORALean.NN.Theorems.SuffExplanationExactOfReducesAt
import CORALean.NN.Theorems.SuffExplanationExactOfRefined
import CORALean.NN.Theorems.SuffExplanationMono
import CORALean.NN.Theorems.SuffExplanationOfEnclose
import CORALean.NN.Theorems.SuffExplanationOfExact
import CORALean.NN.Theorems.SuffExplanationOfNeuronMerging
import CORALean.NN.Theorems.SuffExplanationRefined
import CORALean.NN.Theorems.SuffExplanationTransfer
import CORALean.NN.Theorems.ToLayerSound
import CORALean.NN.Theorems.SmoothNetworkCoraCounterexample
import CORALean.NN.Theorems.SmoothNetworkOutputFnZero
import CORALean.NN.Theorems.VerifySplitSound
import CORALean.NN.Theorems.VerifySplitWithSound
import CORALean.NN.Theorems.SnakeOrderMultiset
import CORALean.NN.Theorems.InputNeuronOrderPerm
import CORALean.NN.Theorems.WeightAccPushLinearEval
import CORALean.NN.Theorems.WeightAccPushAffineEval
import CORALean.NN.Theorems.WeightAccLayerEval
import CORALean.NN.Theorems.WeightNetworkNormalFormAuxEval
import CORALean.NN.Theorems.WeightNetworkNormalFormEval
import CORALean.NN.Theorems.RefinableNetworkMemRefinableLayers
import CORALean.NN.Theorems.ActivationKindMergeValuesIff
import CORALean.NN.Theorems.CatTransformerOuter
import CORALean.NN.Theorems.CatReluOnEvalIff
import CORALean.NN.Theorems.CatImageSubsetOfTransformer
import CORALean.NN.Theorems.SubsetCnfOfMeetEqBot
import CORALean.NN.Theorems.CatEvalAffineIff
import CORALean.NN.Theorems.CatEvalCompIff
import CORALean.NN.Theorems.CatMaxSegmentEvalIff
import CORALean.NN.Theorems.CatMaxSegmentsEvalIff
import CORALean.NN.Theorems.CatMaxPoolEvalIff

/-!
# What a network's enclosure guarantees, collected

`EncloseOuter`/`ImageSubset` are the graph induction; `Verified` composes `holds_of_outer`, read by
`MemSafeSet`/`NotMemUnsafeSet`, and `HoldsOfCheck` computes it; `Robustness` builds on `MarginDir`,
`Misclassified`, `DisjointMisclassifiedOfBounds`, `Classifies`; `HoldsOfSplit`/`VerifySplit*` split.
`LinearWithErrorZero`, `NeuronMergingOuter`, `NeuronMergingNetworkOuter`, `MergeError*` are
neuron merging [1]: error-free linear layers, bucket containment, the Minkowski split, tolerated
by `ExistsMergeTolerance`; `MergeBucketMono`/`MergeBucketCardMono`/`ExistsMergeBucketAll` grow it.
`EncloseNotMonotone` forces `ReducesAt` into one induction — `HoldsOfReducesAt` is [1, Thm. 1] —
and [1, Algs. 1-3] are sound at every scalar (`ReduceOnTheFlyOuter`, `HoldsOfReduceOnTheFly`,
`CompressionPreprocessingOuter`, `BucketToleranceApprox`); `Real/` holds what needs ℝ.

`SuffExplanation`, `MinSuffExplanation` and their `Abstract` and `Exact` forms are local
explanations [2]. `SuffExplanationTransfer`/`OfExact` carry sufficiency to the original network,
`SuffExplanationRefined` and `MinSuffExplanationAbstractOfMin`/`OfRefined` carry it enclosure to
enclosure; the `ExactOfRefined` pair with `SuffExplanationExactOfReducesAt` is [2, Prop. 3] and
its discharge, `MinSuffExplanationCounterexample` and `SuffExplanationConverseFails` its limits.
`SensitivityFDeriv` is what the refinement heuristic [3] rests on: the backpropagated Jacobian
identified with `fderiv` wherever `EvalDifferentiable` holds, which `SensitivityOfMatrix` hands
to `SensitivityLinear`/`SensitivityActivation`; `ReluNotDifferentiable` is why ReLU gets none.
`AtScheduleEval`/`EncloseAtOuter`/`EncloseAtInflate` are the refinement loop [3, Thm. 4.14], its
hypothesis discharged by the `...Converges` files at one, two [3, Prop. 4.13] and three layers.
`Cat*` is AI2: `CatTransformerOuter` is [4, Thm. 1], the `...EvalIff` files the CAT forms' values.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
* [2] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [3] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
* [4] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/
