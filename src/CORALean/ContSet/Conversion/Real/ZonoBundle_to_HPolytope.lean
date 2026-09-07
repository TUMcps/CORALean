import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

/-!
# A bundle's halfspaces, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own halfspace description.
Whichever component `i` names already throws away every other one the bundle
intersects against — the whole point of a bundle being that the intersection is
tighter than any one member. The halfspace step is exact only on the directions
the caller names, as `Zonotope.subset_hPolytope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q : ℕ}

def ZonoBundle.hPolytope (B : ZonoBundle (Vec ℝ n)) (i : Fin B.k)
    (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) : HPolytope (Vec ℝ n) :=
  (B.zonotope i).hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.subset_hPolytope (B : ZonoBundle (Vec ℝ n)) (i : Fin B.k)
    (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    B.construct ⊆ (B.hPolytope i Aq).construct :=
  subset_trans (B.subset_zonotope i) (Zonotope.subset_hPolytope _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
