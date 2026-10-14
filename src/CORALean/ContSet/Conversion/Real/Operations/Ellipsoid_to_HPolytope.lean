module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

@[expose] public section

/-!
# An ellipsoid as halfspaces — the construction

`Ellipsoid.hPolytope` is the construction; `Ellipsoid_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.hPolytope (E : Ellipsoid n) (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    HPolytope (Vec ℝ n) :=
  E.zonotope.hPolytope Aq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
