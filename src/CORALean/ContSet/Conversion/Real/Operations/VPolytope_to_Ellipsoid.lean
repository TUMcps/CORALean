module

public import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A hull as an ellipsoid — the construction

`VPolytope.ellipsoid` is the construction; `VPolytope_to_Ellipsoid` states and proves what it
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

noncomputable def VPolytope.ellipsoid (P : VPolytope (Vec ℝ n)) : Ellipsoid n :=
  P.zonotope.ellipsoid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
