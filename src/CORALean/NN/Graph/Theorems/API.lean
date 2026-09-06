import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
import CORALean.NN.Graph.Theorems.DegreeAtEq
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter
import CORALean.NN.Graph.Theorems.PoolingExact
import CORALean.NN.Graph.Theorems.UncertainAdjExact
import CORALean.NN.Graph.Theorems.UncertainDegreeBounds

/-!
# What the graph layers guarantee

The two layer guarantees are equalities and not enclosures, and both are
`PolyZonotope.map_exact` at a linear map — the graph layers of [1] lose nothing
at a known graph, so every outer approximation a graph neural network pays is
paid by an activation layer or, once the graph is uncertain, by an edge.

Neither assumes anything about the message-passing matrix, which is what lets an
enclosure of it replace the exact one later without restating them.

`UncertainAdjExact` is a third equality, one directory over from the layers: the
uncertain adjacency is exactly the set of adjacencies its edges allow, so an
uncertain graph structure is *represented* without loss even though propagating
it will not be. `DegreeAtEq` writes the degree affinely in the edge weights and
`UncertainDegreeBounds` is where the loss starts — an interval rather than a set
of degrees — carrying the lower bound of `1` that keeps an inverse square root of
the degree total.

`MessagePassingEnclosureOuter` is the one enclosure here rather than an equality,
and it spends that bound: at any admissible edge weights the graph's own
`D̃^(-1/2) Ã D̃^(-1/2)` is a *point* of the enclosure, reached by the factor vector
that pairs each edge weight with the residual the relaxation left at each node.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/
