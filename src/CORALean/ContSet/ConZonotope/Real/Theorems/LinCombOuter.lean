import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.ZonotopeOuter

/-!
# `ConZonotope.linComb` encloses every segment between the two

Both endpoints lie in the enclosing zonotopes, so the segment between them lies
in the zonotopes' `linComb`, which is what the result denotes.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem ConZonotope.linComb_outer (C₁ C₂ : ConZonotope α) :
    segments C₁.construct C₂.construct ⊆ (C₁.linComb C₂).construct := by
  have hlc : (C₁.linComb C₂).construct = (C₁.zonotope.linComb C₂.zonotope).construct :=
    (Zonotope.conZonotope_exact _).symm
  rw [hlc]
  refine subset_trans ?_ (Zonotope.linComb_outer C₁.zonotope C₂.zonotope)
  rintro _ ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  exact ⟨y₁, ConZonotope.zonotope_outer C₁ hy₁, y₂, ConZonotope.zonotope_outer C₂ hy₂,
    lam, hlam, rfl⟩

end CORALean.Real
