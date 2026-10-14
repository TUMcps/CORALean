module

public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A constrained zonotope as an ellipsoid — the construction

`ConZonotope.ellipsoid` is the construction; `ConZonotope_to_Ellipsoid` states and proves what it
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

noncomputable def ConZonotope.ellipsoid (cZ : ConZonotope (Vec ℝ n)) : Ellipsoid n :=
  cZ.zonotope.ellipsoid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
