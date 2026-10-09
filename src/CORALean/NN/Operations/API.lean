import CORALean.NN.Operations.AtSchedule
import CORALean.NN.Operations.BisectBucketTolerance
import CORALean.NN.Operations.Bucketed
import CORALean.NN.Operations.BucketTolerance
import CORALean.NN.Operations.ChainEval
import CORALean.NN.Operations.CompressionPreprocessing
import CORALean.NN.Operations.Convergent
import CORALean.NN.Operations.DifferentiableChain
import CORALean.NN.Operations.DynamicMergeBuckets
import CORALean.NN.Operations.Enclose
import CORALean.NN.Operations.EncloseAt
import CORALean.NN.Operations.Eval
import CORALean.NN.Operations.ExplainBox
import CORALean.NN.Operations.ExplanationRefineLoop
import CORALean.NN.Operations.GreedyAbstractExplanation
import CORALean.NN.Operations.GreedyExplanationStep
import CORALean.NN.Operations.GreedyMinimalExplanation
import CORALean.NN.Operations.GrowBucketTolerance
import CORALean.NN.Operations.InitMergeBuckets
import CORALean.NN.Operations.InMergeBucket
import CORALean.NN.Operations.IntervalChainBackprop
import CORALean.NN.Operations.IntervalChainFwd
import CORALean.NN.Operations.IntervalChainJvp
import CORALean.NN.Operations.LayerRefinable
import CORALean.NN.Operations.LayerSensitivity
import CORALean.NN.Operations.MaxOver
import CORALean.NN.Operations.MergeCols
import CORALean.NN.Operations.MergeRows
import CORALean.NN.Operations.MergeRowWeight
import CORALean.NN.Operations.MinOver
import CORALean.NN.Operations.NetworkConvergent
import CORALean.NN.Operations.PropagateBounds
import CORALean.NN.Operations.Raise
import CORALean.NN.Operations.Ratio
import CORALean.NN.Operations.ReducedLinearIdentity
import CORALean.NN.Operations.ReducedLinearToLayer
import CORALean.NN.Operations.ReduceOnTheFly
import CORALean.NN.Operations.ReduceOnTheFlyFrom
import CORALean.NN.Operations.ReducibleNetworkToNetwork
import CORALean.NN.Operations.RefinableLayerAtPattern
import CORALean.NN.Operations.RefinableNetworkEval
import CORALean.NN.Operations.RefinableNetworkLength
import CORALean.NN.Operations.Refine
import CORALean.NN.Operations.RefineLayer
import CORALean.NN.Operations.RefineLoop
import CORALean.NN.Operations.EncloseReduceAt
import CORALean.NN.Operations.RefineVerifyFrom
import CORALean.NN.Operations.RefineVerify
import CORALean.NN.Operations.RefinementLipschitz
import CORALean.NN.Operations.RefinementNeuron
import CORALean.NN.Operations.RefinementRank
import CORALean.NN.Operations.RefinementRankAll
import CORALean.NN.Operations.RefinementRankApproxError
import CORALean.NN.Operations.RefinementRankLayerBias
import CORALean.NN.Operations.RefinementRankSensitivity
import CORALean.NN.Operations.RefineWorst
import CORALean.NN.Operations.ScheduleCons
import CORALean.NN.Operations.ScheduleHead
import CORALean.NN.Operations.ScheduleTail
import CORALean.NN.Operations.Backprop
import CORALean.NN.Operations.FgsmAttack
import CORALean.NN.Operations.PgdAttack
import CORALean.NN.Operations.PgdStep
import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Operations.StaticMergeBuckets
import CORALean.NN.Operations.ToLayer
import CORALean.NN.Operations.VerifySplit
import CORALean.NN.Operations.VerifySplitWith
import CORALean.NN.Operations.SmoothNetworkEval
import CORALean.NN.Operations.SmoothNetworkNu
import CORALean.NN.Operations.SmoothNetworkToNonlinearSysDT
import CORALean.NN.Operations.ToNonlinearSysDT
import CORALean.NN.Operations.WorstIndex
import CORALean.NN.Operations.SnakeOrder
import CORALean.NN.Operations.InputNeuronOrder
import CORALean.NN.Operations.WeightLayerEval
import CORALean.NN.Operations.WeightNetworkEval
import CORALean.NN.Operations.WeightAccEval
import CORALean.NN.Operations.WeightAccPushLinear
import CORALean.NN.Operations.WeightAccPushAffine
import CORALean.NN.Operations.WeightAccLayer
import CORALean.NN.Operations.WeightNetworkNormalFormAux
import CORALean.NN.Operations.WeightNetworkNormalForm
import CORALean.NN.Operations.RefinableNetworkLayers
import CORALean.NN.Operations.RefinableNetworkRefinableLayers
import CORALean.NN.Operations.ActivationKindMergeValues
import CORALean.NN.Operations.CatTransformer
import CORALean.NN.Operations.CatReluOn
import CORALean.NN.Operations.CatMaxSegment
import CORALean.NN.Operations.CatMaxSegments
import CORALean.NN.Operations.CatMaxPool

/-!
# What a network does, collected

`Enclose` is the pipeline; `ToLayer` nests a sub-network as a layer; `VerifySplit(With)` recurses
`Enclose` over a spec's check (a checker); `ChainEval` is an exact chain's composite. `ExplainBox`
is the set an explanation query asks over, `GreedyMinimalExplanation` (`GreedyExplanationStep`)
and `GreedyAbstractExplanation` (`ExplanationRefineLoop`) the searches for one.
`LayerSensitivity` and `Sensitivity` backpropagate the Jacobian a refinement heuristic weights a
neuron's error by; `DifferentiableChain` is when `SensitivityFDeriv` makes it the derivative.

A schedule, the refinement loop's state, is taken apart by `ScheduleHead`/`ScheduleTail` and
built by `ScheduleCons`, `Raise`/`Refine`/`RefineLayer`/`RefineLoop`; `AtSchedule`/`EncloseAt`
read one against a network through `RefinableLayerAtPattern`, `LayerRefinable` a layer with
nothing to spend, `RefinableNetworkEval`/`Length` the network's map and length.
`RefinementRank*`/`WorstIndex`/`RefineWorst`/`RefinementNeuron` pick where a step goes;
`Convergent`/`NetworkConvergent`/`RefinementLipschitz` are the convergence hypotheses.

Network reduction, written once over the scalar: `BucketTolerance` is [1, Alg. 1], out of
`MaxOver`, `MinOver`, `Ratio`, the merge-bucket builders and its two loops; `ReduceOnTheFly` is
[1, Alg. 2], `ReduceOnTheFlyFrom` its loop and `MergeRows`/`MergeCols` [1, Prop. 4];
`CompressionPreprocessing` is [1, Alg. 3], `ReducedLinearIdentity` its kernel.
`ReducedLinearToLayer`/`ReducibleNetworkToNetwork` lay a reducible network out as layers;
`MergeRowWeight`/`Bucketed` are a merge's cost factor and count.
`CatTransformer` is [2, Fig. 8]; `CatReluOn`, `CatMaxPool` (`CatMaxSegment(s)`) AI2's CAT forms.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
* [2] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/
