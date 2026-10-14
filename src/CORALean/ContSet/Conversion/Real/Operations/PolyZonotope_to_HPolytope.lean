module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

@[expose] public section

/-!
# A polynomial zonotope as halfspaces — the construction

`PolyZonotope.hPolytope` is the construction; `PolyZonotope_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.hPolytope (pZ : PolyZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  pZ.zonotope.hPolytope Aq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
