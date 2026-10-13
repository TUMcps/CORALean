module

public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection

@[expose] public section

/-!
# `HPolytope.cartProd`, over a floating-point scalar

CORA's `@polytope/cartProd_` for two halfspace polytopes: the rows of `P₁` padded with zero
columns on the right, the rows of `P₂` padded with zero columns on the left, and the two row
lists stacked, `A = [A₁ 0; 0 A₂]`, `b = [b₁; b₂]`. Padding and stacking only copy and
concatenate entries, so nothing is computed and nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.cartProd (P₁ : HPolytope 𝕋 (Vec 𝕋 n₁)) (P₂ : HPolytope 𝕋 (Vec 𝕋 n₂)) : HPolytope
    𝕋 (Vec 𝕋 (n₁ + n₂)) :=
  (P₁.padLeft n₂).intersection (HPolytope.padRight n₁ P₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
