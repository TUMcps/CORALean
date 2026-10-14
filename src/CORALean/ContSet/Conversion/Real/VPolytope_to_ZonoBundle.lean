module

public import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_ZonoBundle

@[expose] public section

/-!
# A hull as a bundle of one

Through the hull's own box's zonotope, then `Zonotope.zonoBundle` — the
single-member bundle, exact by `Set.iInter_const`. All the loss is the box
route's, so this is no worse than `VPolytope → Zonotope` already is.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.zonoBundle_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.zonoBundle.construct :=
  subset_trans P.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
