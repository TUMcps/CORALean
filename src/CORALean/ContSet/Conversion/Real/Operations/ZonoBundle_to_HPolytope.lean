module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

@[expose] public section

/-!
# A bundle's halfspaces, at one component — the construction

`ZonoBundle.hPolytope` is the construction; `ZonoBundle_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.hPolytope (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k)
    (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) : HPolytope (Vec ℝ n) :=
  (zB.zonotope i).hPolytope Aq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
