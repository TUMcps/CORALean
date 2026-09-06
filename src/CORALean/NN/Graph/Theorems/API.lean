import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.ConvExactOfAdjacency
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
it will not be. `UncertainDegreeBounds` is where the loss starts — an interval
rather than a set of degrees — and it carries the lower bound of `1` that keeps
an inverse square root of the degree total, which is the fact the enclosure of
`x ↦ x^(-1/2)` will be asked for.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/
