import CORALean.ContSet.HPolytope.Float.Operations.Certified

/-!
# The float certified Minkowski sum encloses

One line, exactly as in the exact layer: `plusOf` is `ofBounds` over directions
the caller named, and the certificates were composed to speak about the sum. The
rounding was paid inside that composition, so this proof never mentions it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}
variable {P₁ P₂ : HPolytope 𝕋 n}

theorem HPolytope.plusOf_outer (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) :
    P₁.construct + P₂.construct ⊆ (HPolytope.plusOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float
