import CORALean.NN.NeuralNetwork

/-!
# Differentiable layer by layer, along the forward pass

The hypothesis the chain rule needs, and it is not `DifferentiableAt ℝ nn.eval x`:
a composite can be differentiable where a factor is not — a linear layer with
`W = 0` after a ReLU computes a constant — so the composite's own
differentiability says nothing about the product of the layers' Jacobians, which
is what `NeuralNetwork.sensitivity` computes.

Each layer is asked at the point the forward pass hands it, which is why this
recurses through `L.eval x` rather than quantifying over the input.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

def NeuralNetwork.DifferentiableChain :
    ∀ {n m : ℕ}, NeuralNetwork S n m → Vec ℝ n → Prop
  | _, _, .nil, _ => True
  | _, _, .cons L rest, x => DifferentiableAt ℝ L.eval x ∧ rest.DifferentiableChain (L.eval x)

end CORALean.Real
