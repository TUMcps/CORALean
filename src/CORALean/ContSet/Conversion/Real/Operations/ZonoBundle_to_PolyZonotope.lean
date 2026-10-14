module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A bundle's polynomial zonotope, at one component — the construction

`ZonoBundle.polyZonotope` is the construction; `ZonoBundle_to_PolyZonotope` states and proves what
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

def ZonoBundle.polyZonotope (zB : ZonoBundle α) (i : Fin zB.k) : PolyZonotope α :=
  (zB.zonotope i).polyZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
