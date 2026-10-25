module

public import CORALean.NN.Definitions.Chain
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

/-!
# Differentiable layer by layer, along the forward pass

The hypothesis the chain rule needs, and it is not `DifferentiableAt ℝ c.eval x`:
a composite can be differentiable where a factor is not — a linear layer with
`W = 0` after a ReLU computes a constant — so the composite's own
differentiability says nothing about the product of the layers' Jacobians, which
is what `Chain.sensitivity` computes.

Each map is asked at the point the forward pass hands it, which is why this
recurses through `f x` rather than quantifying over the input.

## Inputs
* none

## Output
* every layer is differentiable at the point it receives
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

def Chain.IsDifferentiableChain : ∀ {n m : ℕ}, Chain n m → Vec ℝ n → Prop
  | _, _, .nil, _ => True
  | _, _, .cons f rest, x => DifferentiableAt ℝ f x ∧ rest.IsDifferentiableChain (f x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
