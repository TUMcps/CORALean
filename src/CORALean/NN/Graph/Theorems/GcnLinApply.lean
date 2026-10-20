module

public import CORALean.NN.Graph.Operations.GcnLin

@[expose] public section

/-!
# `gcnLin` unfolds to `P H W`

The linear map's associativity read back into the matrix product it packages,
which is what `Theorems/ConvExact` composes with `PolyZonotope.map_exact`.

## Inputs
* `P` – message-passing matrix
* `W` – weight matrix
* `H` – node-feature matrix

## Hypotheses
* none

## Conclusion
* the linear map applies the matrix product P H W
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
