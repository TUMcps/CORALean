import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
import CORALean.NN.Graph.Theorems.ConvUncertainExact
import CORALean.NN.Graph.Theorems.DegreeAtEq
import CORALean.NN.Graph.Theorems.EvalStepsSubmatrix
import CORALean.NN.Graph.Theorems.GcnSharedExact
import CORALean.NN.Graph.Theorems.GcnSharedPoint
import CORALean.NN.Graph.Theorems.GcnStepsExact
import CORALean.NN.Graph.Theorems.GcnStepsOuter
import CORALean.NN.Graph.Theorems.GcnStepsPoint
import CORALean.NN.Graph.Theorems.GcnUncertainOuter
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter
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
edges allow, so representing it costs nothing even though propagating it will. `DegreeAtEq` writes
the degree affinely in the edge weights, and `UncertainDegreeBounds` is where the loss starts — an
interval, not a set of degrees — carrying the lower bound of `1` that keeps the inverse root total.

`MessagePassingEnclosureOuter` is the one enclosure rather than an equality: at any admissible edge
weights the graph's own `D̃^(-1/2) Ã D̃^(-1/2)` is a *point* of it. `ConvUncertainExact` and
`GcnSharedExact` are equalities again — the layer loses nothing beyond what that enclosure already
cost, so charging it twice would overstate the price of an uncertain graph.

`GcnStepsExact` carries that to `L + 1` steps by induction, `GcnSharedPoint` and `GcnStepsPoint`
supplying the point each step lands on. `GcnUncertainOuter` and `GcnStepsOuter` are the statements
a caller wants — what the graph itself computes, over one step or many, lies in the output.

`SubmatrixMulOfClosed` is `[1, §4.3]`'s locality at one step — restricting after multiplying equals
multiplying the restrictions once `hclosed` says nothing outside the subgraph feeds in —
and `EvalStepsSubmatrix` carries that over a whole chain: the same matrix, not an enclosure of one.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/
