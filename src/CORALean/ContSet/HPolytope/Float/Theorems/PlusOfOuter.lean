module

public import CORALean.ContSet.HPolytope.Float.Operations.PlusOf
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.SubsetOfBounds

@[expose] public section

/-!
# The float certified Minkowski sum encloses

One line, exactly as in the exact layer: `plusOf` is `ofBounds` over directions
the caller named, and the certificates were composed to speak about the sum. The
rounding was paid inside that composition, so this proof never mentions it.

## Inputs
* `Aq` – `q × n` matrix

## Hypotheses
* `u₁` – a float bound of `P₁.toSet` along each row
* `u₂` – a float bound of `P₂.toSet` along each row

## Conclusion
* the float certified Minkowski sum encloses
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}
variable {P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.plusOf_outer (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.toSet (Real.HPolytope.rowLin (toRealMat Aq) i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.toSet (Real.HPolytope.rowLin (toRealMat Aq) i)) :
    P₁.toSet + P₂.toSet ⊆ (HPolytope.plusOf Aq u₁ u₂).toSet :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
