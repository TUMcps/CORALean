module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# An ellipsoid as a polynomial zonotope — the construction

`Ellipsoid.polyZonotope` is the construction; `Ellipsoid_to_PolyZonotope` states and proves what it
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

noncomputable def Ellipsoid.polyZonotope (E : Ellipsoid n) : PolyZonotope (Vec ℝ n) :=
  E.zonotope.polyZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
