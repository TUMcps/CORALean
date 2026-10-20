module

public import CORALean.NN.Graph.Operations.Basic
public import CORALean.NN.Graph.Operations.LinearLin

@[expose] public section

/-!
# CORA's `nnGNNLinearLayer` on a point

`evaluateNumeric`: `r = aux_affineMap(obj, input, true)`, which is `H Wᵀ` plus the bias row
at every node. The node features are taken as the matrix `H` itself: CORA's reshape of the
stacked vector is the same data.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `H` – node-feature matrix

## Output
* node features after the linear layer
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer `H ↦ H Wᵀ + 1 bᵀ`. -/
def GNN.linear (W : Mat ℝ F₂ F₁) (b : Vec ℝ F₂) (H : Mat ℝ N F₁) : Mat ℝ N F₂ :=
  GNN.linearLin W H + GNN.linearBias N b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
