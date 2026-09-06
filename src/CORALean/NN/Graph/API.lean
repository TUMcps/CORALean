import CORALean.NN.Graph.Conv
import CORALean.NN.Graph.MessagePassingEnclosure
import CORALean.NN.Graph.Pooling
import CORALean.NN.Graph.SqrtBroadcast
import CORALean.NN.Graph.Uncertain
import CORALean.NN.Graph.UncertainAdjPad
import CORALean.NN.Graph.UncertainDegree
import CORALean.NN.Graph.UncertainSqrt
import CORALean.NN.Graph.Theorems.API

/-!
# Graph neural networks, collected

[1]'s two layers at a known graph — `Conv` is `H ↦ P H W`, `Pooling` the sum across
nodes — are both linear, so both propagate by `PolyZonotope.map` and both are *exact*.

The other half is an uncertain graph: `Uncertain` and `UncertainDegree` weigh an edge
anywhere in `[0,1]`, one factor each, and bracket the degree away from zero, and
`UncertainSqrt` reads `D̃^(-1/2)` off that bracket affinely in those factors plus a
residual. `MessagePassingEnclosure` is `Ã_ij ⬝ s_i ⬝ s_j`, twice `bilin` at the
entrywise product over `UncertainAdjPad` and `SqrtBroadcast`, all over one shared
`m + N` factors, so an edge recurring thrice counts once. `𝒫 H W` is not here yet.

**Where the matrix shape lives.** In the ambient type of the set, not in an index on
`Layer`. `PolyZonotope α` is generic at `[AddCommGroup α] [Module ℝ α]` and `Mat ℝ n c`
has both, so `PolyZonotope (Mat ℝ n c)` is [1]'s matrix polynomial zonotope with
nothing added, as `Zonotope (Mat ℝ n m)` is CORA's `matZonotope`. Nothing here is a
`Layer`: a `Layer` carries an inclusion along a chain, and these carry an equality
`map_exact` proves at every type at once. Re-indexing `Layer` by a `List ℕ` shape would
deliver the wrong ambient type — `Tensor ℝ [n, c]` is `Mat ℝ n c` up to `rfl` only,
instance search sees through neither, and `P H W` is matrix multiplication.

`sumPool` is the seam: it lands in `Vec ℝ c`, so a graph network's output is a
`NeuralNetwork` input unchanged. Real only, `Float.PolyZonotope` being vector-shaped.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/
