module

public import CORALean.NN.Graph.Theorems.AdjAtSupportSubset
public import CORALean.NN.Graph.Theorems.AdjAtSymm
public import CORALean.NN.Graph.Theorems.BallEnumBallEnumIdx
public import CORALean.NN.Graph.Theorems.BallEnumInjective
public import CORALean.NN.Graph.Theorems.BallEqOfSuccEq
public import CORALean.NN.Graph.Theorems.BallMono
public import CORALean.NN.Graph.Theorems.BallMonoOfSupport
public import CORALean.NN.Graph.Theorems.BallSubsetReduceKeep
public import CORALean.NN.Graph.Theorems.BallSubsetSucc
public import CORALean.NN.Graph.Theorems.ConvExact
public import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
public import CORALean.NN.Graph.Theorems.ConvUncertainExact
public import CORALean.NN.Graph.Theorems.DegreeAtEq
public import CORALean.NN.Graph.Theorems.DegreeSubmatrixOfBall
public import CORALean.NN.Graph.Theorems.DegreeSubmatrixOfBallUncertain
public import CORALean.NN.Graph.Theorems.Basic
public import CORALean.NN.Graph.Theorems.EdgeMatSymm
public import CORALean.NN.Graph.Theorems.EvalStepsRowBall
public import CORALean.NN.Graph.Theorems.EvalStepsRowBallEnum
public import CORALean.NN.Graph.Theorems.EvalStepsRowBallOfAdjacency
public import CORALean.NN.Graph.Theorems.EvalStepsRowBallOfAdjacencyUncertain
public import CORALean.NN.Graph.Theorems.EvalStepsRowMask
public import CORALean.NN.Graph.Theorems.EvalStepsRowMaskUncertain
public import CORALean.NN.Graph.Theorems.EvalStepsSubmatrix
public import CORALean.NN.Graph.Theorems.ExistsBallStable
public import CORALean.NN.Graph.Theorems.GcnLinApply
public import CORALean.NN.Graph.Theorems.GcnSharedExact
public import CORALean.NN.Graph.Theorems.GcnSharedP
public import CORALean.NN.Graph.Theorems.GcnSharedPoint
public import CORALean.NN.Graph.Theorems.GcnStepsExact
public import CORALean.NN.Graph.Theorems.GcnStepsOuter
public import CORALean.NN.Graph.Theorems.GcnStepsP
public import CORALean.NN.Graph.Theorems.GcnStepsPoint
public import CORALean.NN.Graph.Theorems.GcnUncertainOuter
public import CORALean.NN.Graph.Theorems.LinearPolyZonotopeExact
public import CORALean.NN.Graph.Theorems.MemBallEnumIff
public import CORALean.NN.Graph.Theorems.MemBallSelf
public import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing
public import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter
public import CORALean.NN.Graph.Theorems.MessagePassingNeZero
public import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBall
public import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBallUncertain
public import CORALean.NN.Graph.Theorems.NotMemBallOfIsolated
public import CORALean.NN.Graph.Theorems.OneLeDegree
public import CORALean.NN.Graph.Theorems.PoolingExact
public import CORALean.NN.Graph.Theorems.ReduceGNNForNodeExact
public import CORALean.NN.Graph.Theorems.ReducedStepsRow
public import CORALean.NN.Graph.Theorems.SelectMul
public import CORALean.NN.Graph.Theorems.SelectMatToReal
public import CORALean.NN.Graph.Theorems.SelectMulTranspose
public import CORALean.NN.Graph.Theorems.SmulEdgeHalf
public import CORALean.NN.Graph.Theorems.SqrtAffine
public import CORALean.NN.Graph.Theorems.SubmatrixMulOfClosed
public import CORALean.NN.Graph.Theorems.SumPoolLinApply
public import CORALean.NN.Graph.Theorems.UncertainAdjExact
public import CORALean.NN.Graph.Theorems.UncertainDegreeBounds
public import CORALean.NN.Graph.Theorems.SumPoolLinPermInvariant
public import CORALean.NN.Graph.Theorems.RowEqMask
public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowMask
public import CORALean.NN.Graph.Theorems.EvalStepsLayersSubmatrix
public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowBall
public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowBallEnum
public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowBallOfAdjacencyUncertain
public import CORALean.NN.Graph.Theorems.BfsVisitedEqBall
public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowBfsUncertain
public import CORALean.NN.Graph.Theorems.EvalLayersMemGcnActSteps
public import CORALean.NN.Graph.Theorems.EvalLayersMemGcnActStepsUncertain
public import CORALean.NN.Graph.Theorems.TailEncloseMem
public import CORALean.NN.Graph.Theorems.Alg1NodeSound
public import CORALean.NN.Graph.Theorems.Alg1GraphSound
public import CORALean.NN.Graph.Theorems.FloatBiasPointMem
public import CORALean.NN.Graph.Theorems.FloatGcnOuter
public import CORALean.NN.Graph.Theorems.FloatLinearOuter
public import CORALean.NN.Graph.Theorems.FloatRightMatMulVec
public import CORALean.NN.Graph.Theorems.FloatSumPoolOuter
public import CORALean.NN.Graph.Theorems.ReducedStepsFloatOuter
public import CORALean.NN.Graph.Theorems.ReduceGNNForNodeFloatOuter
public import CORALean.NN.Graph.Theorems.BallSubsetReduceKeepFloat

/-!
# What the graph layers guarantee

The two layer guarantees at a known graph are equalities, not enclosures: both are
`PolyZonotope.map_exact` at a linear map — `GcnLinApply`/`SelectMul`/`SumPoolLinApply` unfold the
maps themselves — so every outer approximation a graph network pays is paid by an activation
layer or an edge, never a graph layer that assumes nothing of `P`.

`UncertainAdjExact`/`SmulEdgeHalf` is a third equality; `DegreeAtEq`/`UncertainDegreeBounds`/
`OneLeDegree`/`EdgeMatNonneg` write and bracket the uncertain degree, `SqrtAffine` the relaxation
read over it. `MessagePassingEnclosureOuter` is the one enclosure — a *point* of it — carried
through by `ConvUncertainExact`/`GcnSharedExact`/`MatMulBilinApply`/`GcnSharedP`/`GcnStepsExact`/
`GcnStepsP`, `GcnStepsOuter` the bound a caller wants.

`SubmatrixMulOfClosed`/`EvalStepsSubmatrix`/`SelectMulTranspose` are `[1, §4.3]`'s locality given
`hclosed`; supplied at a mask by `EvalStepsRowMask`, or needing none by `EvalStepsRowBall`, its `κ`
built by `BallEnumInjective`/`MemBallEnumIff`/`BallEnumIdx`/`BallEnumBallEnumIdx` into
`EvalStepsRowBallEnum`. `DegreeSubmatrixOfBall`/`MessagePassingSubmatrixOfBall` need the ring one
hop past the ball; `EvalStepsRowBallOfAdjacency` composes both into row `v`.

`BallMonoOfSupport`/`AdjAtSupportSubset` carry locality to an uncertain graph, `adjMax A U` (every
edge at `1`) dominating every admissible `adjAt`'s support and hence its ball, sizing
`EvalStepsRowMaskUncertain`'s `S`; `AdjAtSymm` gives `adjAt` the symmetry
`DegreeSubmatrixOfBallUncertain`/`MessagePassingSubmatrixOfBallUncertain` need, uniformly in `lam`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/
