import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
import CORALean.NN.Graph.Theorems.ConvUncertainExact
import CORALean.NN.Graph.Theorems.DegreeAtEq
import CORALean.NN.Graph.Theorems.GcnUncertainOuter
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter
import CORALean.NN.Graph.Theorems.PoolingExact
import CORALean.NN.Graph.Theorems.UncertainAdjExact
import CORALean.NN.Graph.Theorems.UncertainDegreeBounds

/-!
# What the graph layers guarantee

The two layer guarantees at a known graph are equalities and not enclosures, and both are
`PolyZonotope.map_exact` at a linear map — the graph layers of [1] lose nothing there, so every
outer approximation a graph neural network pays is paid by an activation layer or, once the graph
is uncertain, by an edge. Neither assumes anything about the message-passing matrix, so an
enclosure of it replaces the exact one later without restating them.

`UncertainAdjExact` is a third equality, one directory over: the uncertain adjacency is exactly
the set of adjacencies its edges allow, so an uncertain graph structure is *represented* without
loss even though propagating it will not be. `DegreeAtEq` writes the degree affinely in the edge
weights and `UncertainDegreeBounds` is where the loss starts — an interval rather than a set of
degrees — carrying the lower bound of `1` that keeps the inverse square root total.

`MessagePassingEnclosureOuter` is the one enclosure rather than an equality, and it spends that
bound: at any admissible edge weights the graph's own `D̃^(-1/2) Ã D̃^(-1/2)` is a *point* of it,
reached by the factor vector pairing each edge weight with the residual the relaxation left.
`ConvUncertainExact` is an equality again, on purpose: the node features' factors are disjoint
from the edges', so `𝒫 H W` loses nothing beyond what that enclosure already cost, and charging it
twice would overstate the price of an uncertain graph. `GcnUncertainOuter` puts the two together
into the statement a caller wants — the layer the graph itself computes, at any point of the
feature set, lies in the output.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/
