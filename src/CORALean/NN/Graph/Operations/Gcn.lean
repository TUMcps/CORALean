module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.NN.Graph.Operations.GcnLin

@[expose] public section

/-!
# The graph convolutional layer on a matrix polynomial zonotope

CORA's `nnGCNLayer`, [1, Def. 4] and [1, Prop. 2]: the layer *is* a linear map
of matrices, so its propagation is `PolyZonotope.map` at `gcnLin` and nothing
else — the whole of what CORA's layer computes at a graph with no uncertain
edges, and why [1] records that this layer induces no outer approximation.

## Inputs
* `P` – message-passing matrix
* `W` – weight matrix
* `pZ` – node features as a polynomial zonotope

## Output
* polynomial zonotope of the layer's output

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer on a matrix polynomial zonotope, which is the whole of what CORA's
`nnGCNLayer` computes at a graph with no uncertain edges. -/
def GNN.gcn (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (pZ : PolyZonotope (Mat ℝ N F₁)) :
    PolyZonotope (Mat ℝ N F₂) := pZ.map (GNN.gcnLin P W)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
