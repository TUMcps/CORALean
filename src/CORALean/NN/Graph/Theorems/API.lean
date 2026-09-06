import CORALean.NN.Graph.Theorems.ConvExact
import CORALean.NN.Graph.Theorems.PoolingExact

/-!
# What the fixed-graph layers guarantee

Both guarantees are equalities and not enclosures, and both are
`PolyZonotope.map_exact` at a linear map — the graph layers of [1] lose nothing
at a known graph, so every outer approximation a graph neural network pays is
paid by an activation layer or, once the graph is uncertain, by an edge.

Neither theorem assumes anything about the message-passing matrix, which is what
lets an enclosure of it replace the exact one later without restating them.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/
