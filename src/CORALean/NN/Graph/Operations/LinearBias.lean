import CORALean.Global.Scalar

/-!
# The bias of CORA's `nnGNNLinearLayer`

`output + obj.b'`: the bias row is added to every node's feature row.
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

/-- The bias `b` repeated for each of the `N` nodes. -/
def GNN.linearBias (N : ℕ) (b : Vec ℝ F₂) : Mat ℝ N F₂ :=
  Matrix.of fun _ f => b f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
