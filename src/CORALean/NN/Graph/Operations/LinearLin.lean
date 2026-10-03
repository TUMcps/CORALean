import CORALean.ContSet.ContSet.ContSet

/-!
# The linear part of CORA's `nnGNNLinearLayer`

`aux_affineMap` reshapes the `n·k` node features to an `n × k` matrix `H` and multiplies by
`Wᵀ`: `H ↦ H Wᵀ`, the weight `W` having one row per output feature.
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

/-- `H ↦ H Wᵀ`, `W` of one row per output feature. -/
def GNN.linearLin (W : Mat ℝ F₂ F₁) : Mat ℝ N F₁ →ₗ[ℝ] Mat ℝ N F₂ :=
  matMulRight Wᵀ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
