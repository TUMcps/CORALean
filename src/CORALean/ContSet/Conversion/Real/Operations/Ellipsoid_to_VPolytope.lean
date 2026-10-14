module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

@[expose] public section

/-!
# An ellipsoid as its corners — the construction

`Ellipsoid.vPolytope` is the construction; `Ellipsoid_to_VPolytope` states and proves what it
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

noncomputable def Ellipsoid.vPolytope (E : Ellipsoid n) : VPolytope (Vec ℝ n) :=
  E.zonotope.vPolytope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
