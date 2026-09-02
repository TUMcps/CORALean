import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter

/-!
# `ConZonotope.linComb` encloses every segment between the two

Both endpoints lie in the enclosing zonotopes, so the segment lies in their
`linComb`, and adding no constraints loses nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem ConZonotope.linComb_outer (C₁ C₂ : ConZonotope 𝕋 n) :
    segments C₁.construct C₂.construct ⊆ (C₁.linComb C₂).construct := by
  refine subset_trans ?_ (Zonotope.conZonotope_outer _)
  refine subset_trans ?_ (Zonotope.linComb_outer C₁.zonotope C₂.zonotope)
  rintro _ ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  exact ⟨y₁, ConZonotope.zonotope_outer C₁ hy₁, y₂, ConZonotope.zonotope_outer C₂ hy₂,
    lam, hlam, rfl⟩

end CORALean.Float
