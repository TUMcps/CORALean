import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

/-!
# A constrained zonotope as halfspaces

Constraints dropped, then the zonotope answers each direction by summing
absolute values. Loose by exactly the constraints thrown away; tight would mean
a linear program per direction over the coefficient domain, which is
`HPolytope.ofBounds` with certificates the caller supplies.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

def ConZonotope.hPolytope (C : ConZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  C.zonotope.hPolytope Aq

theorem ConZonotope.subset_hPolytope (C : ConZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    C.construct ⊆ (C.hPolytope Aq).construct :=
  subset_trans C.zonotope_outer (Zonotope.subset_hPolytope _ _)


end CORALean.Real
