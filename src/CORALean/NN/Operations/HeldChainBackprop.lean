module

public import CORALean.NN.Definitions.HeldChain
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The backpropagation of a network with its slopes held

CORA's `neuralNetwork/backpropZonotopeBatch` without `exact_backprop`, for one gradient: from the
last layer to the first, a linear layer maps the gradient `g` at its output to `Wᵀ g` at its input
(`nnLinearLayer/backpropZonotopeBatch`, `gc = W' gc`, `gG = W' gG`), and an activation layer scales
it by the slopes `m` its forward pass stored (`nnActivationLayer/backpropZonotopeBatch`, `gc = gc .*
m`, `gG(:, genIds) = gG(:, genIds) .* m`). The center's gradient and every generator's are each one
such pass; a generator that a layer added for its approximation errors has no column at the layers
before it (`gG(:, max(genIds)+1:end) = []`), so its pass ends there.

## Inputs
* none

## Output
* the gradient at the input from the gradient at the output
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HeldChain.backprop : ∀ {n k : ℕ}, HeldChain n k → Vec ℝ k → Vec ℝ n
  | _, _, .nil, g => g
  | _, _, .linear W rest, g => Wᵀ *ᵥ rest.backprop g
  | _, _, .slope s rest, g => fun i => s i * rest.backprop g i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
