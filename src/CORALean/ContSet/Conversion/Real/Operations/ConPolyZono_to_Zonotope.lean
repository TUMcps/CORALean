module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A constrained polynomial zonotope as a zonotope — the construction

`ConPolyZono.zonotope` is the construction; `ConPolyZono_to_Zonotope` states and proves what it
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

def ConPolyZono.zonotope (cPZ : ConPolyZono α) : Zonotope α :=
  cPZ.polyZonotope.zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
