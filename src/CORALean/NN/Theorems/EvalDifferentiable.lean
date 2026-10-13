module

public import CORALean.NN.Operations.ChainEval
public import CORALean.NN.Operations.DifferentiableChain
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# A differentiable chain evaluates differentiably

One direction, and composition is the whole proof. The converse fails: a linear
layer with `W = 0` after a ReLU computes a constant, differentiable everywhere,
while the ReLU under it is differentiable at no zero coordinate.

What `SensitivityFDeriv` needs before it can apply `fderiv_comp`, which asks for
the tail's differentiability at the head's output.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.differentiableAt_eval : ∀ {n m : ℕ} (c : Chain n m)
    (x : Vec ℝ n), c.DifferentiableChain x → DifferentiableAt ℝ c.eval x
  | _, _, .nil, _, _ => differentiableAt_id
  | _, _, .cons f rest, x, h => by
      -- the recursive `DifferentiableChain` is a conjunction only after unfolding
      obtain ⟨hf, hrest⟩ : DifferentiableAt ℝ f x ∧ rest.DifferentiableChain (f x) := h
      exact (rest.differentiableAt_eval _ hrest).comp x hf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
