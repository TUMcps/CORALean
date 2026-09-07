import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.VPolytope_to_PolyZonotope

/-!
# A hull as a constrained polynomial zonotope

Through the hull's own box and that box's zonotope, then the zonotope's exact
reading as a polynomial zonotope, then `PolyZonotope.conPolyZono` — an empty
constraint system, so that last leg adds nothing and is exact. All the loss is
the box route's, exactly as in `VPolytope.polyZonotope_contains`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.conPolyZono (P : VPolytope (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  P.polyZonotope.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.conPolyZono_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.conPolyZono.construct :=
  subset_trans P.polyZonotope_contains (PolyZonotope.conPolyZono_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
