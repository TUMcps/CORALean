module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.VPolytope_to_PolyZonotope

@[expose] public section

/-!
# A hull as a constrained polynomial zonotope — the construction

`VPolytope.conPolyZono` is the construction; `VPolytope_to_ConPolyZono` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.conPolyZono (P : VPolytope (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  P.polyZonotope.conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
