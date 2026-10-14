module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Ellipsoid

@[expose] public section

/-!
# A constrained polynomial zonotope as an ellipsoid — the construction

`ConPolyZono.ellipsoid` is the construction; `ConPolyZono_to_Ellipsoid` states and proves what it
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

noncomputable def ConPolyZono.ellipsoid (cPZ : ConPolyZono (Vec ℝ n)) : Ellipsoid n :=
  cPZ.polyZonotope.ellipsoid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
