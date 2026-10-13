module

public import CORALean.NN.Graph.Operations.MatMulBilin

@[expose] public section

/-!
# `matMulBilin` unfolds to plain matrix multiplication

The bundling adds nothing to read back: applying the bilinear map is `rfl`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem GNN.matMulBilin_apply (X : Mat ℝ N F₁) (Y : Mat ℝ F₁ F₂) :
    GNN.matMulBilin N F₁ F₂ X Y = X * Y := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
