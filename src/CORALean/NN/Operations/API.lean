module

public import CORALean.NN.Operations.AtSchedule
public import CORALean.NN.Operations.Bucketed
public import CORALean.NN.Operations.BucketTolerance
public import CORALean.NN.Operations.ChainEval
public import CORALean.NN.Operations.CompressionPreprocessing
public import CORALean.NN.Operations.IsConvergent
public import CORALean.NN.Operations.IsDifferentiableChain
public import CORALean.NN.Operations.Enclose
public import CORALean.NN.Operations.EncloseAt
public import CORALean.NN.Operations.Eval
public import CORALean.NN.Operations.ExplainBox
public import CORALean.NN.Operations.ExplanationRefineLoop
public import CORALean.NN.Operations.GreedyAbstractExplanation
public import CORALean.NN.Operations.GreedyMinimalExplanation
public import CORALean.NN.Operations.GrowBucketTolerance
public import CORALean.NN.Operations.InitMergeBuckets
public import CORALean.NN.Operations.IntervalChainBackprop
public import CORALean.NN.Operations.IntervalChainFwd
public import CORALean.NN.Operations.IntervalChainJvp
public import CORALean.NN.Operations.LayerRefinable
public import CORALean.NN.Operations.LayerSensitivity
public import CORALean.NN.Operations.MarginDir
public import CORALean.NN.Operations.MaxOver
public import CORALean.NN.Operations.MergeCols
public import CORALean.NN.Operations.MergeRows
public import CORALean.NN.Operations.MergeRowWeight
public import CORALean.NN.Operations.MinOver
public import CORALean.NN.Operations.NetworkConvergent
public import CORALean.NN.Operations.PropagateBounds
public import CORALean.NN.Operations.Raise
public import CORALean.NN.Operations.Ratio
public import CORALean.NN.Operations.ReducedLinearIdentity
public import CORALean.NN.Operations.ReducedLinearToLayer
public import CORALean.NN.Operations.ReduceOnTheFly
public import CORALean.NN.Operations.ReduceOnTheFlyFrom
public import CORALean.NN.Operations.ReducibleNetworkToNetwork
public import CORALean.NN.Operations.RefinableLayerAtPattern
public import CORALean.NN.Operations.RefinableNetworkEval
public import CORALean.NN.Operations.RefinableNetworkLength
public import CORALean.NN.Operations.Refine
public import CORALean.NN.Operations.RefineLayer
public import CORALean.NN.Operations.RefineLoop
public import CORALean.NN.Operations.EncloseReduceAt
public import CORALean.NN.Operations.RefineVerifyFrom
public import CORALean.NN.Operations.RefineVerify
public import CORALean.NN.Operations.RefinementLipschitz
public import CORALean.NN.Operations.RefinementNeuron
public import CORALean.NN.Operations.RefinementRank
public import CORALean.NN.Operations.RefinementRankAll
public import CORALean.NN.Operations.RefinementRankLayerBias
public import CORALean.NN.Operations.RefineWorst
public import CORALean.NN.Operations.ScheduleCons
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Operations.Backprop
public import CORALean.NN.Operations.FgsmAttack
public import CORALean.NN.Operations.PgdAttack
public import CORALean.NN.Operations.PgdStep
public import CORALean.NN.Operations.Sensitivity
public import CORALean.NN.Operations.ToLayer
public import CORALean.NN.Operations.VerifySplit
public import CORALean.NN.Operations.VerifySplitWith
public import CORALean.NN.Operations.SmoothNetworkEval
public import CORALean.NN.Operations.SmoothNetworkNu
public import CORALean.NN.Operations.SmoothNetworkToNonlinearSysDT
public import CORALean.NN.Operations.SmoothNetworkOutputFn
public import CORALean.NN.Operations.WorstIndex
public import CORALean.NN.Operations.SnakeOrder
public import CORALean.NN.Operations.InputNeuronOrder
public import CORALean.NN.Operations.WeightLayerEval
public import CORALean.NN.Operations.WeightAccLayer
public import CORALean.NN.Operations.WeightNetworkNormalFormAux
public import CORALean.NN.Operations.WeightNetworkNormalForm
public import CORALean.NN.Operations.RefinableNetworkLayers
public import CORALean.NN.Operations.RefinableNetworkRefinableLayers
public import CORALean.NN.Operations.ActivationKindMergeValues
public import CORALean.NN.Operations.CatTransformer
public import CORALean.NN.Operations.CatReluOn
public import CORALean.NN.Operations.CatMaxSegment
public import CORALean.NN.Operations.CatMaxSegments
public import CORALean.NN.Operations.CatMaxPool
public import CORALean.NN.Operations.IntervalChainFwdFloat
public import CORALean.NN.Operations.IntervalChainBackpropFloat
public import CORALean.NN.Operations.EncloseUnsafeInputs
public import CORALean.NN.Operations.UnsafeInputConstraints
public import CORALean.NN.Operations.Verify
public import CORALean.NN.Operations.IntervalChainToChain
public import CORALean.NN.Operations.IntervalChainBackpropAtFloat
public import CORALean.NN.Operations.IntervalChainSensitivityFloat
public import CORALean.NN.Operations.FgsmAttackFloat
public import CORALean.NN.Operations.PgdAttackFloat
public import CORALean.NN.Operations.WeightAccPushLinearFloat
public import CORALean.NN.Operations.WeightAccPushAffineFloat
public import CORALean.NN.Operations.WeightAccLayerFloat
public import CORALean.NN.Operations.WeightNetworkNormalFormAuxFloat
public import CORALean.NN.Operations.WeightNetworkNormalFormFloat
public import CORALean.NN.Operations.InputNeuronOrderFloat

/-!
# What a network does, collected

`Enclose` is the pipeline; `ToLayer` nests a sub-network as a layer; `VerifySplit(With)` recurses
`Enclose` over a spec's check (a checker); `ChainEval` is an exact chain's composite. `ExplainBox`
is the set an explanation query asks over, `GreedyMinimalExplanation`
and `GreedyAbstractExplanation` (`ExplanationRefineLoop`) the searches for one.
`LayerSensitivity` and `Sensitivity` backpropagate the Jacobian a refinement heuristic weights a
neuron's error by; `IsDifferentiableChain` is when `SensitivityFDeriv` makes it the derivative.

A schedule, the refinement loop's state, is taken apart by `ScheduleHead`/`ScheduleTail` and
built by `ScheduleCons`, `Raise`/`Refine`/`RefineLayer`/`RefineLoop`; `AtSchedule`/`EncloseAt`
read one against a network through `RefinableLayerAtPattern`, `LayerRefinable` a layer with
nothing to spend, `RefinableNetworkEval`/`Length` the network's map and length.
`RefinementRank*`/`WorstIndex`/`RefineWorst`/`RefinementNeuron` pick where a step goes;
`IsConvergent`/`NetworkConvergent`/`RefinementLipschitz` are the convergence hypotheses.

Network reduction, written once over the scalar: `BucketTolerance` is [1, Alg. 1], out of
`MaxOver`, `MinOver`, `Ratio`, the merge-bucket builders and its two loops; `ReduceOnTheFly` is
[1, Alg. 2], `ReduceOnTheFlyFrom` its loop and `MergeRows`/`MergeCols` [1, Prop. 4];
`CompressionPreprocessing` is [1, Alg. 3], `ReducedLinearIdentity` its kernel.
`ReducedLinearToLayer`/`ReducibleNetworkToNetwork` lay a reducible network out as layers;
`MergeRowWeight`/`Bucketed` are a merge's cost factor and count.
`CatTransformer` is [2, Fig. 8]; `CatReluOn`, `CatMaxPool` (`CatMaxSegment(s)`) AI2's CAT forms.

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
* [2] [T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2: Safety
      and Robustness Certification of Neural Networks with Abstract Interpretation". 2018 IEEE
      Symposium on Security and Privacy (SP), 2018.](../../../../references/2018/gehr-sp-ai2.md)
-/
