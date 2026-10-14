module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConZonotope

@[expose] public section

/-!
# A constrained polynomial zonotope as a constrained zonotope — the construction

`ConPolyZono.conZonotope` is the construction; `ConPolyZono_to_ConZonotope` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.conZonotope (cPZ : ConPolyZono α) : ConZonotope α :=
  cPZ.polyZonotope.conZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
