import CORALean.NN.Operations.Sensitivity

/-!
# Backpropagating a gradient through a network

CORA's `backprop`, on the numeric gradient: from the output end, each layer maps the
gradient it receives at its output to one at its input by its transposed Jacobian,
`g ← Jᵢᵀ g`. Written as the recursion the chain already is: the rest of the network's
backpropagated gradient at this layer's output, then this layer's own step.

The interval and zonotope batch variants of CORA's `backprop` are not this.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The gradient `g` at the output, pulled back to the input `x`, one transposed layer
Jacobian at a time. -/
noncomputable def Chain.backprop : ∀ {n m : ℕ}, Chain n m → Vec ℝ n → Vec ℝ m → Vec ℝ n
  | _, _, .nil, _, g => g
  | _, _, .cons f rest, x, g => (layerSensitivity f x)ᵀ *ᵥ rest.backprop (f x) g

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
