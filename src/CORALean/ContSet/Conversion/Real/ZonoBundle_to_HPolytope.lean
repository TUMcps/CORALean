module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_HPolytope

@[expose] public section

/-!
# A bundle's halfspaces, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own halfspace description.
Whichever component `i` names already throws away every other one the bundle
intersects against — the whole point of a bundle being that the intersection is
tighter than any one member. The halfspace step is exact only on the directions
the caller names, as `Zonotope.hPolytope_contains` already is.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.hPolytope_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k)
    (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    zB.construct ⊆ (zB.hPolytope i Aq).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.hPolytope_contains _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
