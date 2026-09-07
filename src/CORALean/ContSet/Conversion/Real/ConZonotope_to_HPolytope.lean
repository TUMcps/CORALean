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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

def ConZonotope.hPolytope (cZ : ConZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  cZ.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.hPolytope_contains (cZ : ConZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    cZ.construct ⊆ (cZ.hPolytope Aq).construct :=
  subset_trans cZ.zonotope_contains (Zonotope.hPolytope_contains _ _)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
