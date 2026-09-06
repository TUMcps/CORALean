import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
import CORALean.NN.Graph.Theorems.ConvUncertainExact
import CORALean.NN.Graph.Theorems.DegreeAtEq
import CORALean.NN.Graph.Theorems.GcnSharedExact
import CORALean.NN.Graph.Theorems.GcnSharedPoint
import CORALean.NN.Graph.Theorems.GcnStepsExact
import CORALean.NN.Graph.Theorems.GcnStepsOuter
import CORALean.NN.Graph.Theorems.GcnStepsPoint
import CORALean.NN.Graph.Theorems.GcnUncertainOuter
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter
import CORALean.NN.Graph.Theorems.PoolingExact
import CORALean.NN.Graph.Theorems.UncertainAdjExact
import CORALean.NN.Graph.Theorems.UncertainDegreeBounds

/-!
# What the graph layers guarantee

The two layer guarantees at a known graph are equalities, not enclosures, and both are
`PolyZonotope.map_exact` at a linear map — [1]'s graph layers lose nothing there, so every outer
approximation a graph network pays is paid by an activation layer or by an edge. Neither assumes
anything of the message-passing matrix, so an enclosure of it replaces the exact one later.

`UncertainAdjExact` is a third equality: the uncertain adjacency is exactly the adjacencies its
edges allow, so an uncertain graph structure is *represented* without loss though propagating it
will not be. `DegreeAtEq` writes the degree affinely in the edge weights and `UncertainDegreeBounds`
is where the loss starts — an interval, not a set of degrees — carrying the lower bound of `1` that
keeps the inverse square root total.

`MessagePassingEnclosureOuter` is the one enclosure rather than an equality, and it spends that
bound: at any admissible edge weights the graph's own `D̃^(-1/2) Ã D̃^(-1/2)` is a *point* of it.
`ConvUncertainExact` and `GcnSharedExact` are equalities again, on purpose: the layer loses nothing
beyond what that enclosure already cost, and charging it twice would overstate the price of an
uncertain graph.

`GcnStepsExact` carries that to `L + 1` steps by induction, `GcnSharedPoint` and `GcnStepsPoint`
supplying the point each step lands on; at `L = 0` it would fail, the chain being `H` with its
independent block untouched. `GcnUncertainOuter` and `GcnStepsOuter` are the statements a caller
wants — what the graph itself computes, over one step or many, lies in the output.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/
