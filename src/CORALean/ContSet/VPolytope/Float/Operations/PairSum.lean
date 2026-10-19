module

public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.pairSum`

The pairwise vertex sums of two vertex descriptions, rounded whichever way is
asked.

## Inputs
* `add` – rounded addition
* `P₁` – first polytope
* `P₂` – second polytope

## Output
* all sums of a vertex of `P₁` and one of `P₂`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pairwise vertex sums, rounded whichever way is asked. -/
def VPolytope.pairSum (add : 𝕋 → 𝕋 → 𝕋) (P₁ P₂ : VPolytope (Vec 𝕋 n)) :
    Fin (P₁.k * P₂.k) → Vec 𝕋 n :=
  fun l i => add (P₁.V (finProdFinEquiv.symm l).1 i) (P₂.V (finProdFinEquiv.symm l).2 i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
