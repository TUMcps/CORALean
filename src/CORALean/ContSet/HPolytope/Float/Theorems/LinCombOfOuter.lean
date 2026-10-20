module

public import CORALean.ContSet.HPolytope.Float.Operations.LinCombOf
public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# The float certified convex combination encloses

The same line as `plusOf_outer` at a different composition of bounds, and it
holds for the same reason: `ofBounds` says exactly what the bounds handed to it
say, rounding included.

## Inputs
* `Aq` – `q × n` matrix

## Hypotheses
* `u₁` – a float bound of `P₁.construct` along each row
* `u₂` – a float bound of `P₂.construct` along each row

## Conclusion
* the float certified convex combination encloses
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}
variable {P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.linCombOf_outer (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) :
    Set.linComb P₁.construct P₂.construct ⊆ (HPolytope.linCombOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
