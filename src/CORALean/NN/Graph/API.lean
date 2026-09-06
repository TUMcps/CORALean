import CORALean.NN.Graph.Conv
import CORALean.NN.Graph.Pooling
import CORALean.NN.Graph.Theorems.API

/-!
# Graph neural networks at a fixed graph, collected

[1]'s two graph layers with the node features uncertain and the graph known:
`Conv` is `H ↦ P H W`, `Pooling` the summation across nodes. Both are linear, so
both propagate by `PolyZonotope.map` and both are *exact* — the whole of [1]'s
claim that these layers induce no outer approximation.

**Where the matrix shape lives.** In the ambient type of the set, not in an index
on `Layer`. `PolyZonotope α` is generic at `[AddCommGroup α] [Module ℝ α]` and
`Mat ℝ n c` has both, so `PolyZonotope (Mat ℝ n c)` is [1]'s matrix polynomial
zonotope with nothing added, as `Zonotope (Mat ℝ n m)` is CORA's `matZonotope`.
Nothing here is a `Layer`: a `Layer` carries an inclusion along a chain, and
these carry an equality `map_exact` proves at every ambient type at once.
Re-indexing `Layer` by a `List ℕ` shape would instead deliver the wrong ambient
type — `Tensor ℝ [n, c]` is `Mat ℝ n c` up to `rfl` only, instance search sees
through neither, and `P H W` is matrix multiplication.

`sumPool` is the seam: it lands in `Vec ℝ c`, so a graph network's output is a
`NeuralNetwork` input unchanged, and [1, Def. 7] crosses it the same way for the
activation layers.

Real only, because `Float.PolyZonotope` is indexed by ℕ over `Vec`: a float
matrix polynomial zonotope is a representation to build, not a layer.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/
