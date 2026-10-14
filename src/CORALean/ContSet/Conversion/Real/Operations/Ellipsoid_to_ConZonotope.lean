module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

@[expose] public section

/-!
# An ellipsoid as a constrained zonotope — the construction

`Ellipsoid.conZonotope` is the construction; `Ellipsoid_to_ConZonotope` states and proves what it
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

noncomputable def Ellipsoid.conZonotope (E : Ellipsoid n) : ConZonotope (Vec ℝ n) :=
  E.zonotope.conZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
