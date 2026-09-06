import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

/-!
# A hull as an ellipsoid

Through the zonotope the hull's own box gives. A direct minimum-volume
enclosing ellipsoid of a vertex list is a separate piece of mathematics, and
this composition is not it.

Loses whatever the zonotope route loses on top of the box the hull already
loses to.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.ellipsoid (P : VPolytope (Vec ℝ n)) : Ellipsoid n :=
  P.zonotope.ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.ellipsoid_outer (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.ellipsoid.construct :=
  subset_trans P.subset_zonotope (Zonotope.ellipsoid_outer _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
