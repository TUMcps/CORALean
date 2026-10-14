module

public import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# A hull as a bundle of one — the construction

`VPolytope.zonoBundle` is the construction; `VPolytope_to_ZonoBundle` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.zonoBundle (P : VPolytope (Vec ℝ n)) : ZonoBundle (Vec ℝ n) :=
  P.zonotope.zonoBundle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
