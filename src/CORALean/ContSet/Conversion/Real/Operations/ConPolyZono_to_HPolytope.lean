module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_HPolytope

@[expose] public section

/-!
# A constrained polynomial zonotope as halfspaces — the construction

`ConPolyZono.hPolytope` is the construction; `ConPolyZono_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {qI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConPolyZono.hPolytope (cPZ : ConPolyZono α) (Aq : Fin qI → (α →ₗ[ℝ] ℝ)) :
    HPolytope α :=
  cPZ.polyZonotope.hPolytope Aq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
