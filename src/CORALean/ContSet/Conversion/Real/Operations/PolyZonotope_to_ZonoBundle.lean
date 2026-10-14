module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A polynomial zonotope as a bundle of one — the construction

`PolyZonotope.zonoBundle` is the construction; `PolyZonotope_to_ZonoBundle` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.zonoBundle (pZ : PolyZonotope α) : ZonoBundle α :=
  pZ.zonotope.zonoBundle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
