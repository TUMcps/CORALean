import CORALean.NN.Graph.Theorems.AdjAtSupportSubset
import CORALean.NN.Graph.Theorems.BallEnumBallEnumIdx
import CORALean.NN.Graph.Theorems.BallEnumIdx
import CORALean.NN.Graph.Theorems.BallEnumInjective
import CORALean.NN.Graph.Theorems.BallMono
import CORALean.NN.Graph.Theorems.BallMonoOfSupport
import CORALean.NN.Graph.Theorems.BallSubsetSucc
import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
import CORALean.NN.Graph.Theorems.ConvUncertainExact
import CORALean.NN.Graph.Theorems.DegreeAtEq
import CORALean.NN.Graph.Theorems.EvalStepsRowBall
import CORALean.NN.Graph.Theorems.EvalStepsRowBallEnum
import CORALean.NN.Graph.Theorems.EvalStepsRowMask
import CORALean.NN.Graph.Theorems.EvalStepsRowMaskUncertain
import CORALean.NN.Graph.Theorems.EvalStepsSubmatrix
import CORALean.NN.Graph.Theorems.GcnSharedExact
import CORALean.NN.Graph.Theorems.GcnSharedPoint
import CORALean.NN.Graph.Theorems.GcnStepsExact
import CORALean.NN.Graph.Theorems.GcnStepsOuter
import CORALean.NN.Graph.Theorems.GcnStepsPoint
import CORALean.NN.Graph.Theorems.GcnUncertainOuter
import CORALean.NN.Graph.Theorems.MemBallEnumIff
import CORALean.NN.Graph.Theorems.MemBallSelf
import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter
import CORALean.NN.Graph.Theorems.MessagePassingNeZero
import CORALean.NN.Graph.Theorems.PoolingExact
import CORALean.NN.Graph.Theorems.SubmatrixMulOfClosed
import CORALean.NN.Graph.Theorems.UncertainAdjExact
import CORALean.NN.Graph.Theorems.UncertainDegreeBounds

/-!
# What the graph layers guarantee

The two layer guarantees at a known graph are equalities, not enclosures: both are
`PolyZonotope.map_exact` at a linear map, so every outer approximation a graph network pays is paid
by an activation layer or an edge, never by a graph layer that assumes nothing of `P`.

`UncertainAdjExact` is a third equality; `DegreeAtEq` writes the degree affinely in the edge
weights, and `UncertainDegreeBounds` brackets it, keeping the root's lower bound at `1`.
`MessagePassingEnclosureOuter` is the one enclosure: at any admissible weights the graph's own
`D̃^(-1/2) Ã D̃^(-1/2)` is a *point* of it, carried through by `ConvUncertainExact`/`GcnSharedExact`
and `GcnStepsExact`, `GcnSharedPoint`/`GcnStepsPoint`/`GcnUncertainOuter`/`GcnStepsOuter` the point
and the statement a caller wants.

`SubmatrixMulOfClosed`/`EvalStepsSubmatrix` are `[1, §4.3]`'s locality given `hclosed`, supplied by
`EvalStepsRowMask` at a mask or, needing none, by `EvalStepsRowBall` itself — `[1, §4.3]` proper.
`MemBallSelf`/`BallSubsetSucc`/`BallMono`/`MemBallSuccOfMessagePassing`/`MessagePassingNeZero` are
the ball's own facts; `BallEnumInjective`/`MemBallEnumIff`/`BallEnumIdx`/`BallEnumBallEnumIdx` build
the `κ` `EvalStepsRowBall` asks for, and `EvalStepsRowBallEnum` instantiates it for a caller.

`BallMonoOfSupport`/`AdjAtSupportSubset` carry that locality to an uncertain graph: nonnegativity
makes `adjMax A U` (every edge at `1`) dominate every admissible `adjAt`'s support, hence its ball.
`EvalStepsRowMaskUncertain` is the uniform result: one `S` sized against that ball serves every
`lam`, via `EvalStepsRowMask`'s inclusion — `EvalStepsRowBall`'s exact `hκ` does not compose.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/
