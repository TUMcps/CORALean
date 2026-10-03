import CORALean.NN.Graph.Operations.LinearBias
import CORALean.NN.Graph.Operations.LinearLin

/-!
# CORA's `nnGNNLinearLayer` on a point

`evaluateNumeric`: `r = aux_affineMap(obj, input, true)`, which is `H Wᵀ` plus the bias row
at every node. The node features are taken as the matrix `H` itself: CORA's reshape of the
stacked vector is the same data.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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
