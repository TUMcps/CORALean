import CORALean.ContSet.HPolytope.Float.Operations.Certified

/-!
# The float certified operations enclose

One line each, exactly as in the exact layer: each is `ofBounds` over directions
the caller named, and the certificates were composed to speak about the result.
The rounding was paid inside the composition, so no proof here mentions it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n p : ℕ}
variable {P₁ P₂ P : HPolytope 𝕋 n}

theorem HPolytope.plusOf_outer (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) :
    P₁.construct + P₂.construct ⊆ (HPolytope.plusOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

theorem HPolytope.linCombOf_outer (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) :
    segments P₁.construct P₂.construct ⊆ (HPolytope.linCombOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

theorem HPolytope.mtimesOf_outer (M : Mat 𝕋 p n) (Aq : Mat 𝕋 q p)
    (u : ∀ i, FloatBound 𝕋 P.construct ((rowLin Aq i).comp (mulVecLin (toRealMat M)))) :
    (toRealMat M *ᵥ ·) '' P.construct ⊆ (HPolytope.mtimesOf M Aq u).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float
