module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# An ellipsoid as a bundle of one — the construction

`Ellipsoid.zonoBundle` is the construction; `Ellipsoid_to_ZonoBundle` states and proves what it
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

noncomputable def Ellipsoid.zonoBundle (E : Ellipsoid n) : ZonoBundle (Vec ℝ n) :=
  E.zonotope.zonoBundle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
