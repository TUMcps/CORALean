module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A network with its activation slopes held, for the zonotope batch backpropagation

CORA's `neuralNetwork/backpropZonotopeBatch` without `exact_backprop` takes the gradients at the
output's center and generators back through the layers with every activation's line fixed: the
slopes `m` its forward pass stored (`backprop.store.coeffs`). A linear layer maps a gradient by
`Wᵀ`, an activation layer scales it by `m`, neuron by neuron, and the gradients of the
approximation errors' generators stop at the layer that made them. A chain of those two steps is
`HeldChain`: the linear map `W` (no bias, which a gradient does not see) or the slopes `s`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- A network with its activation slopes held: the identity, a linear map, or the slopes of an
activation layer. -/
inductive HeldChain : ℕ → ℕ → Type where
  | nil {n : ℕ} : HeldChain n n
  | linear {n m k : ℕ} (W : Mat ℝ m n) (rest : HeldChain m k) : HeldChain n k
  | slope {n k : ℕ} (s : Vec ℝ n) (rest : HeldChain n k) : HeldChain n k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
