import CORALean.NN.Graph.Ball
import CORALean.NN.Graph.Conv
import CORALean.NN.Graph.ConvUncertain
import CORALean.NN.Graph.GcnSteps
import CORALean.NN.Graph.Mask
import CORALean.NN.Graph.MessagePassingEnclosure
import CORALean.NN.Graph.Pooling
import CORALean.NN.Graph.SqrtBroadcast
import CORALean.NN.Graph.Subgraph
import CORALean.NN.Graph.Uncertain
import CORALean.NN.Graph.UncertainAdjPad
import CORALean.NN.Graph.UncertainDegree
import CORALean.NN.Graph.UncertainSqrt
import CORALean.NN.Graph.Theorems.API

/-!
# Graph neural networks, collected

[1]'s two layers at a known graph — `Conv` is `H ↦ P H W`, `Pooling` the sum across nodes — are both
linear, so both propagate by `PolyZonotope.map` and both are *exact*. The other half is an uncertain
graph: `Uncertain` and `UncertainDegree` weigh an edge anywhere in `[0,1]`, one factor each, and
bracket the degree away from zero, and `UncertainSqrt` reads `D̃^(-1/2)` off that bracket affinely
in those factors plus a residual. `MessagePassingEnclosure` is `Ã_ij ⬝ s_i ⬝ s_j`, twice `bilin` at
the entrywise product over `UncertainAdjPad` and `SqrtBroadcast`, all over one shared `m + N`
factors, so an edge recurring thrice counts once. `ConvUncertain` multiplies it by an uncertain
`H`: `gcnShared` is `bilin` at matrix multiplication over factors the two sets share,
`gcnUncertain` that after padding each set by the other's, and `GcnSteps` iterates `gcnShared` at
one graph, so an edge weighs the same at every step. `Subgraph` is `[1, Cor. 1]`'s projection
`M`, its products `H' = M H` and `P' = M P Mᵀ` plain `Matrix.submatrix`; `Ball` and `Mask` are
its radius-indexed source, an `r`-hop neighbourhood and what a large enough one lets through.

**Where the matrix shape lives.** In the ambient type of the set, not in an index on `Layer`.
`PolyZonotope α` is generic at `[AddCommGroup α] [Module ℝ α]` and `Mat ℝ n c` has both, so
`PolyZonotope (Mat ℝ n c)` is [1]'s matrix polynomial zonotope with nothing added, as
`Zonotope (Mat ℝ n m)` is CORA's `matZonotope`. Nothing here is a `Layer`: a `Layer` carries an
inclusion along a chain, these an equality `map_exact` proves at every type at once.

`sumPool` is the seam: it lands in `Vec ℝ c`, so a graph network's output is a `NeuralNetwork`
input unchanged. Real only, `Float.PolyZonotope` being vector-shaped.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/
