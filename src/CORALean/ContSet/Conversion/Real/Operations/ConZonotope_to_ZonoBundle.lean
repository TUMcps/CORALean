module

public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# A constrained zonotope as a bundle of one — the construction

`ConZonotope.zonoBundle` is the construction; `ConZonotope_to_ZonoBundle` states and proves what it
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

def ConZonotope.zonoBundle (cZ : ConZonotope α) : ZonoBundle α :=
  cZ.zonotope.zonoBundle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
