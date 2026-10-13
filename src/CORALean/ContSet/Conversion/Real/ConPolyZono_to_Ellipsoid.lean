import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Ellipsoid

/-!
# A constrained polynomial zonotope as an ellipsoid

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own ball. A
two-hop composition, and precision is lost twice over: the constraints go first,
freeing every factor the equalities were confining, and then the sharing goes,
at `PolyZonotope.zonotope`, before the cube-to-ball inflation. For a
representation whose whole point is the constraints, that is a lot to give up,
and none of the three losses is recovered by another.

A direct ellipsoid from a constrained polynomial zonotope is a separate piece of
mathematics and no tighter enclosure is attempted here.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def ConPolyZono.ellipsoid (cPZ : ConPolyZono (Vec ℝ n)) : Ellipsoid n :=
  cPZ.polyZonotope.ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.ellipsoid_contains (cPZ : ConPolyZono (Vec ℝ n)) :
    cPZ.construct ⊆ cPZ.ellipsoid.construct :=
  subset_trans cPZ.polyZonotope_contains (PolyZonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
