module

public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# `HPolytope.cartProd`, over a floating-point scalar

CORA's `@polytope/cartProd_` for two halfspace polytopes: the rows of `P₁` padded with zero
columns on the right, the rows of `P₂` padded with zero columns on the left, and the two row
lists stacked, `A = [A₁ 0; 0 A₂]`, `b = [b₁; b₂]`. Padding and stacking only copy and
concatenate entries, so nothing is computed and nothing rounds. The error box is the two boxes
side by side.

## Inputs
* `P₁` – H-polytope
* `P₂` – H-polytope

## Output
* the Cartesian product, `P₁` and `P₂` padded and their rows stacked
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.cartProd (P₁ : HPolytope 𝕋 (Vec 𝕋 n₁)) (P₂ : HPolytope 𝕋 (Vec 𝕋 n₂)) : HPolytope
    𝕋 (Vec 𝕋 (n₁ + n₂)) :=
  { (P₁.padLeft n₂).stackRows (HPolytope.padRight n₁ P₂) with
    I_error := ⟨Fin.append P₁.I_error.inf P₂.I_error.inf,
      Fin.append P₁.I_error.sup P₂.I_error.sup⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
