module

public import CORALean.ContSet.VPolytope.Float.Operations.Plus
public import CORALean.ContSet.VPolytope.Float.Operations.Unvec
public import CORALean.ContSet.VPolytope.Float.Operations.Vec

@[expose] public section

/-!
# `VPolytope.matPlus`, over a floating-point scalar

CORA's `plus` of matrix polytopes: the pairwise sums of the stacked vertices (`vecVpot`), reshaped
back into matrices. The float version stacks both operands, adds them with `VPolytope.plus` (every
vertex sum rounded down, the gap in the error box) and unstacks. CORA then prunes the sums to the
hull vertices with `convhulln`, which the float version does not.

## Inputs
* `P₁` – first matrix polytope
* `P₂` – second matrix polytope

## Output
* matrix polytope of the pairwise vertex sums
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stacked pairwise sums, unstacked. -/
def VPolytope.matPlus (P₁ P₂ : VPolytope (Mat 𝕋 m n)) : VPolytope (Mat 𝕋 m n) :=
  (P₁.vec.plus P₂.vec).unvec

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
