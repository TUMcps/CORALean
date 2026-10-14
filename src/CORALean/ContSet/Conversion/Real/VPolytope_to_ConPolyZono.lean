module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.VPolytope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_ConPolyZono

@[expose] public section

/-!
# A hull as a constrained polynomial zonotope

Through the hull's own box and that box's zonotope, then the zonotope's exact
reading as a polynomial zonotope, then `PolyZonotope.conPolyZono` — an empty
constraint system, so that last leg adds nothing and is exact. All the loss is
the box route's, exactly as in `VPolytope.polyZonotope_contains`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.conPolyZono_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.conPolyZono.construct :=
  subset_trans P.polyZonotope_contains (PolyZonotope.conPolyZono_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
