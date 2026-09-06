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

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def ConPolyZono.ellipsoid (C : ConPolyZono (Vec ℝ n)) : Ellipsoid n :=
  C.polyZonotope.ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.ellipsoid_outer (C : ConPolyZono (Vec ℝ n)) :
    C.construct ⊆ C.ellipsoid.construct :=
  subset_trans C.polyZonotope_outer (PolyZonotope.ellipsoid_outer _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
