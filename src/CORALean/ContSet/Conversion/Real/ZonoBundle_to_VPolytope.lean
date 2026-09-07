import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# A bundle's corners, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own `2ʰ` sign corners.
Whichever component `i` names already throws away every other one the bundle
intersects against — the whole point of a bundle being that the intersection is
tighter than any one member. The corner step is exact, so all the loss is the
choice of component.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def ZonoBundle.vPolytope (B : ZonoBundle (Vec ℝ n)) (i : Fin B.k) :
    VPolytope (Vec ℝ n) :=
  (B.zonotope i).vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.subset_vPolytope (B : ZonoBundle (Vec ℝ n)) (i : Fin B.k) :
    B.construct ⊆ (B.vPolytope i).construct :=
  subset_trans (B.subset_zonotope i) (Zonotope.subset_vPolytope _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
