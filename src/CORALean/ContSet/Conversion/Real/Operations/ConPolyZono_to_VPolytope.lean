module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_VPolytope

@[expose] public section

/-!
# A constrained polynomial zonotope as its corners — the construction

`ConPolyZono.vPolytope` is the construction; `ConPolyZono_to_VPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConPolyZono.vPolytope (cPZ : ConPolyZono α) : VPolytope α :=
  cPZ.polyZonotope.vPolytope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
