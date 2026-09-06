import CORALean.NN.Graph.Conv
import CORALean.NN.Graph.Pooling
import CORALean.NN.Graph.Uncertain
import CORALean.NN.Graph.UncertainDegree
import CORALean.NN.Graph.Theorems.API

/-!
# Graph neural networks, collected

[1]'s two layers at a known graph: `Conv` is `H ↦ P H W`, `Pooling` the summation
across nodes. Both are linear, so both propagate by `PolyZonotope.map` and both
are *exact* — [1]'s claim that they induce no outer approximation.

`Uncertain` and `UncertainDegree` are the other half: an uncertain edge carries a
weight anywhere in `[0,1]`, so the adjacency is a matrix polynomial zonotope with one
factor per edge, and the degree it feeds is bracketed away from zero. The enclosure
of `D̃^(-1/2) Ã D̃^(-1/2)` that reads those is not here yet.

**Where the matrix shape lives.** In the ambient type of the set, not in an index on
`Layer`. `PolyZonotope α` is generic at `[AddCommGroup α] [Module ℝ α]` and `Mat ℝ n c`
has both, so `PolyZonotope (Mat ℝ n c)` is [1]'s matrix polynomial zonotope with
nothing added, as `Zonotope (Mat ℝ n m)` is CORA's `matZonotope`. Nothing here is a
`Layer`: a `Layer` carries an inclusion along a chain, and these carry an equality
`map_exact` proves at every type at once. Re-indexing `Layer` by a `List ℕ` shape would
deliver the wrong ambient type — `Tensor ℝ [n, c]` is `Mat ℝ n c` up to `rfl` only,
instance search sees through neither, and `P H W` is matrix multiplication.

`sumPool` is the seam: it lands in `Vec ℝ c`, so a graph network's output is a
`NeuralNetwork` input unchanged, and [1, Def. 7] crosses it the same way for the
activation layers. Real only, `Float.PolyZonotope` being vector-shaped.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/
