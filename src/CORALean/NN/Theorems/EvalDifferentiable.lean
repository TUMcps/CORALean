import CORALean.NN.Operations.DifferentiableChain

/-!
# A differentiable chain evaluates differentiably

One direction, and composition is the whole proof. The converse fails: a linear
layer with `W = 0` after a ReLU computes a constant, differentiable everywhere,
while the ReLU under it is differentiable at no zero coordinate.

What `SensitivityFDeriv` needs before it can apply `fderiv_comp`, which asks for
the tail's differentiability at the head's output.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

theorem NeuralNetwork.differentiableAt_eval : ∀ {n m : ℕ} (nn : NeuralNetwork S n m)
    (x : Vec ℝ n), nn.DifferentiableChain x → DifferentiableAt ℝ nn.eval x
  | _, _, .nil, _, _ => differentiableAt_id
  | _, _, .cons L rest, x, h => by
      -- the recursive `DifferentiableChain` is a conjunction only after unfolding
      obtain ⟨hL, hrest⟩ : DifferentiableAt ℝ L.eval x ∧ rest.DifferentiableChain (L.eval x) := h
      exact (rest.differentiableAt_eval _ hrest).comp x hL

end CORALean.Real
