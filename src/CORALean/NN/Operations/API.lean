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
import CORALean.NN.Operations.LayerRefinable
import CORALean.NN.Operations.LayerSensitivity
import CORALean.NN.Operations.MaxOver
import CORALean.NN.Operations.MergeCols
import CORALean.NN.Operations.MergeRows
import CORALean.NN.Operations.MergeRowWeight
import CORALean.NN.Operations.MinOver
import CORALean.NN.Operations.NetworkConvergent
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
import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Operations.StaticMergeBuckets
import CORALean.NN.Operations.ToLayer
import CORALean.NN.Operations.VerifySplit
import CORALean.NN.Operations.WorstIndex

/-!
# What a network does, collected

`Enclose` is the pipeline; `ToLayer` nests a sub-network as a layer; `VerifySplit` recurses
`Enclose` over a checker and a splitter; `ChainEval` is an exact chain's composite. `ExplainBox`
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

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/
