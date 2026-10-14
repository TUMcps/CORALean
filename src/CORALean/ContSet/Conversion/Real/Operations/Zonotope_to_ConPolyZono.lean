module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A zonotope as a constrained polynomial zonotope — the construction

`Zonotope.conPolyZono` is the construction; `Zonotope_to_ConPolyZono` states and proves what it
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

def Zonotope.conPolyZono (Z : Zonotope α) : ConPolyZono α :=
  Z.polyZonotope.conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
