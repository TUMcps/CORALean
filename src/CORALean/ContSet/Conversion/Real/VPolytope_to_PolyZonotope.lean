import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# A hull as a polynomial zonotope

Through the hull's own box and that box's zonotope, then the zonotope's exact
reading as a polynomial zonotope with one factor per generator. A direct
polynomial zonotope from a vertex list is a separate piece of mathematics, and
its dependent structure would go unused here regardless.

Loses whatever the box route loses and nothing further.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.polyZonotope (P : VPolytope (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  P.zonotope.polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.subset_polyZonotope (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.polyZonotope.construct :=
  subset_trans P.subset_zonotope (Zonotope.polyZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
