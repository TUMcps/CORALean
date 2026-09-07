import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

/-!
# A hull as a bundle of one

Through the hull's own box's zonotope, then `Zonotope.zonoBundle` — the
single-member bundle, exact by `Set.iInter_const`. All the loss is the box
route's, so this is no worse than `VPolytope → Zonotope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.zonoBundle (P : VPolytope (Vec ℝ n)) : ZonoBundle (Vec ℝ n) :=
  P.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.zonoBundle_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.zonoBundle.construct :=
  subset_trans P.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
