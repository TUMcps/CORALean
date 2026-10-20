module

public import CORALean.NN.Operations.Backprop

@[expose] public section

/-!
# Backpropagation is the transposed Jacobian applied to the output gradient

`Chain.backprop c x g = (c.sensitivity x)ᵀ *ᵥ g`: pulling `g` back layer by layer is the
transpose of the product of the layer Jacobians, `(AB)ᵀ = BᵀAᵀ`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* backpropagation is the transposed sensitivity applied to the gradient
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.backprop_eq_transpose_mulVec : ∀ {n m : ℕ} (c : Chain n m) (x : Vec ℝ n)
    (g : Vec ℝ m), c.backprop x g = (c.sensitivity x)ᵀ *ᵥ g
  | _, _, .nil, x, g => by
      show g = (1 : Mat ℝ _ _)ᵀ *ᵥ g
      rw [Matrix.transpose_one, Matrix.one_mulVec]
  | _, _, .cons f rest, x, g => by
      show (layerSensitivity f x)ᵀ *ᵥ rest.backprop (f x) g
        = (rest.sensitivity (f x) * layerSensitivity f x)ᵀ *ᵥ g
      rw [Chain.backprop_eq_transpose_mulVec rest (f x) g, Matrix.transpose_mul,
        Matrix.mulVec_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
