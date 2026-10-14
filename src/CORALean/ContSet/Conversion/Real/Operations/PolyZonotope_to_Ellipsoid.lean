module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A polynomial zonotope as an ellipsoid — the construction

`PolyZonotope.ellipsoid` is the construction; `PolyZonotope_to_Ellipsoid` states and proves what it
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

noncomputable def PolyZonotope.ellipsoid (pZ : PolyZonotope (Vec ℝ n)) : Ellipsoid n :=
  pZ.zonotope.ellipsoid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
