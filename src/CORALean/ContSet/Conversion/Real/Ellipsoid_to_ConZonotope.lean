import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

/-!
# An ellipsoid as a constrained zonotope

Through the zonotope, then the constrained zonotope with nothing to satisfy —
the second leg loses nothing, so all the loss is the ellipsoid's own zonotope
step. A direct constrained enclosure is a separate piece of mathematics.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Ellipsoid.conZonotope (E : Ellipsoid n) : ConZonotope (Vec ℝ n) :=
  E.zonotope.conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.conZonotope_contains (E : Ellipsoid n) : E.construct ⊆ E.conZonotope.construct :=
  subset_trans E.zonotope_contains (Zonotope.conZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
