module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A polynomial zonotope as a constrained zonotope — the construction

`PolyZonotope.conZonotope` is the construction; `PolyZonotope_to_ConZonotope` states and proves what
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

def PolyZonotope.conZonotope (pZ : PolyZonotope α) : ConZonotope α :=
  pZ.zonotope.conZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
