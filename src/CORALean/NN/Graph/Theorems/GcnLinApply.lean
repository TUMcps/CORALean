import CORALean.NN.Graph.Operations.GcnLin

/-!
# `gcnLin` unfolds to `P H W`

The linear map's associativity read back into the matrix product it packages,
which is what `Theorems/ConvExact` composes with `PolyZonotope.map_exact`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.gcnLin_apply (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (H : Mat ℝ N F₁) :
    GNN.gcnLin P W H = P * H * W := by
  show P * (H * W) = P * H * W
  rw [Matrix.mul_assoc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
