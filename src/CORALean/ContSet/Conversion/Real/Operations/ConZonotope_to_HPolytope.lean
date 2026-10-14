module

public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

@[expose] public section

/-!
# A constrained zonotope as halfspaces — the construction

`ConZonotope.hPolytope` is the construction; `ConZonotope_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.hPolytope (cZ : ConZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  cZ.zonotope.hPolytope Aq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
