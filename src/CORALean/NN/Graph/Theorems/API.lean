import CORALean.NN.Graph.Theorems.AdjAtSupportSubset
import CORALean.NN.Graph.Theorems.AdjAtSymm
import CORALean.NN.Graph.Theorems.BallEnumBallEnumIdx
import CORALean.NN.Graph.Theorems.BallEnumIdx
import CORALean.NN.Graph.Theorems.BallEnumInjective
import CORALean.NN.Graph.Theorems.BallEqOfSuccEq
import CORALean.NN.Graph.Theorems.BallMono
import CORALean.NN.Graph.Theorems.BallMonoOfSupport
import CORALean.NN.Graph.Theorems.BallSubsetReduceKeep
import CORALean.NN.Graph.Theorems.BallSubsetSucc
import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
import CORALean.NN.Graph.Theorems.ConvUncertainExact
import CORALean.NN.Graph.Theorems.DegreeAtEq
import CORALean.NN.Graph.Theorems.DegreeSubmatrixOfBall
import CORALean.NN.Graph.Theorems.DegreeSubmatrixOfBallUncertain
import CORALean.NN.Graph.Theorems.EdgeMatNonneg
import CORALean.NN.Graph.Theorems.EdgeMatSymm
import CORALean.NN.Graph.Theorems.EvalStepsRowBall
import CORALean.NN.Graph.Theorems.EvalStepsRowBallEnum
import CORALean.NN.Graph.Theorems.EvalStepsRowBallOfAdjacency
import CORALean.NN.Graph.Theorems.EvalStepsRowBallOfAdjacencyUncertain
import CORALean.NN.Graph.Theorems.EvalStepsRowMask
import CORALean.NN.Graph.Theorems.EvalStepsRowMaskUncertain
import CORALean.NN.Graph.Theorems.EvalStepsSubmatrix
import CORALean.NN.Graph.Theorems.ExistsBallStable
import CORALean.NN.Graph.Theorems.GcnLinApply
import CORALean.NN.Graph.Theorems.GcnSharedExact
import CORALean.NN.Graph.Theorems.GcnSharedP
import CORALean.NN.Graph.Theorems.GcnSharedPoint
import CORALean.NN.Graph.Theorems.GcnStepsExact
import CORALean.NN.Graph.Theorems.GcnStepsOuter
import CORALean.NN.Graph.Theorems.GcnStepsP
import CORALean.NN.Graph.Theorems.GcnStepsPoint
import CORALean.NN.Graph.Theorems.GcnUncertainOuter
import CORALean.NN.Graph.Theorems.LinearPolyZonotopeExact
import CORALean.NN.Graph.Theorems.MatMulBilinApply
import CORALean.NN.Graph.Theorems.MemBallEnumIff
import CORALean.NN.Graph.Theorems.MemBallSelf
import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter
import CORALean.NN.Graph.Theorems.MessagePassingNeZero
import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBall
import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBallUncertain
import CORALean.NN.Graph.Theorems.NotMemBallOfIsolated
import CORALean.NN.Graph.Theorems.OneLeDegree
import CORALean.NN.Graph.Theorems.PoolingExact
import CORALean.NN.Graph.Theorems.ReduceGNNForNodeExact
import CORALean.NN.Graph.Theorems.ReduceKeepZeroStepsCora
import CORALean.NN.Graph.Theorems.ReducedStepsRow
import CORALean.NN.Graph.Theorems.SelectMul
import CORALean.NN.Graph.Theorems.SelectMatMul
import CORALean.NN.Graph.Theorems.SelectMatToReal
import CORALean.NN.Graph.Theorems.SelectMulTranspose
import CORALean.NN.Graph.Theorems.SmulEdgeHalf
import CORALean.NN.Graph.Theorems.SqrtAffine
import CORALean.NN.Graph.Theorems.SubmatrixMulOfClosed
import CORALean.NN.Graph.Theorems.SumPoolLinApply
import CORALean.NN.Graph.Theorems.UncertainAdjExact
import CORALean.NN.Graph.Theorems.UncertainDegreeBounds
import CORALean.NN.Graph.Theorems.SumPoolLinPermInvariant

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

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/
