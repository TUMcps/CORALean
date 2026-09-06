import CORALean.NN.Graph.Theorems.BallMono
import CORALean.NN.Graph.Theorems.BallSubsetSucc
import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
import CORALean.NN.Graph.Theorems.ConvUncertainExact
import CORALean.NN.Graph.Theorems.DegreeAtEq
import CORALean.NN.Graph.Theorems.EvalStepsRowBall
import CORALean.NN.Graph.Theorems.EvalStepsRowMask
import CORALean.NN.Graph.Theorems.EvalStepsSubmatrix
import CORALean.NN.Graph.Theorems.GcnSharedExact
import CORALean.NN.Graph.Theorems.GcnSharedPoint
import CORALean.NN.Graph.Theorems.GcnStepsExact
import CORALean.NN.Graph.Theorems.GcnStepsOuter
import CORALean.NN.Graph.Theorems.GcnStepsPoint
import CORALean.NN.Graph.Theorems.GcnUncertainOuter
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

`UncertainAdjExact` is a third equality: the uncertain adjacency is exactly the adjacencies its
edges allow. `DegreeAtEq` writes the degree affinely in the edge weights, and
`UncertainDegreeBounds` brackets it, carrying the lower bound of `1` that keeps the root total.

`MessagePassingEnclosureOuter` is the one enclosure rather than an equality: at any admissible edge
weights the graph's own `D̃^(-1/2) Ã D̃^(-1/2)` is a *point* of it, which `ConvUncertainExact` and
`GcnSharedExact` carry through the layer at no extra cost, `GcnStepsExact` over `L + 1` steps,
`GcnSharedPoint`/`GcnStepsPoint` supplying the point each step lands on, `GcnUncertainOuter` and
`GcnStepsOuter` the statements a caller wants.

`SubmatrixMulOfClosed`/`EvalStepsSubmatrix` are `[1, §4.3]`'s locality at one step and over a whole
chain, given `hclosed`. `MemBallSelf`, `BallSubsetSucc`, `BallMono` and
`MemBallSuccOfMessagePassing`/`MessagePassingNeZero` are the ball's own facts; `EvalStepsRowMask`
supplies `hclosed`'s reason, at a mask rather than a hypothesis, and `EvalStepsRowBall` is
`[1, §4.3]` itself: a ball's own enumeration needs no `hclosed` at all.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/
