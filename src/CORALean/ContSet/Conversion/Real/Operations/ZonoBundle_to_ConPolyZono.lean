module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConPolyZono
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A bundle's constrained polynomial zonotope, at one component — the construction

`ZonoBundle.conPolyZono` is the construction; `ZonoBundle_to_ConPolyZono` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.conPolyZono (zB : ZonoBundle α) (i : Fin zB.k) : ConPolyZono α :=
  (zB.zonotope i).conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
