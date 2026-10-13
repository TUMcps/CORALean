import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# An ellipsoid as a polynomial zonotope

Through the box the ellipsoid gives, then that box's zonotope, then the
zonotope's exact reading as a polynomial zonotope with one factor per
generator. A direct polynomial zonotope from an ellipsoid is a separate piece
of mathematics, and its dependent structure would go unused here regardless.

Loses whatever the box route loses and nothing further.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Ellipsoid.polyZonotope (E : Ellipsoid n) : PolyZonotope (Vec ℝ n) :=
  E.zonotope.polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.polyZonotope_contains (E : Ellipsoid n) :
    E.construct ⊆ E.polyZonotope.construct :=
  subset_trans E.zonotope_contains (Zonotope.polyZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
