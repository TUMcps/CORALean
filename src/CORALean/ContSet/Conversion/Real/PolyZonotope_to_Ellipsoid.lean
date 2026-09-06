import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

/-!
# A polynomial zonotope as an ellipsoid

Through the zonotope enclosure, then that zonotope's `√h` ball. A polynomial
zonotope's set is generally not even convex, so no ellipsoid is exact for it:
this is an enclosure with a precision knob rather than a conversion, and a
direct construction would be tighter.

Loses whatever both steps lose: the zonotope's own enclosure, then the
cube-to-ball inflation.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def PolyZonotope.ellipsoid (PZ : PolyZonotope (Vec ℝ n)) : Ellipsoid n :=
  PZ.zonotope.ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.ellipsoid_outer (PZ : PolyZonotope (Vec ℝ n)) :
    PZ.construct ⊆ PZ.ellipsoid.construct :=
  subset_trans PZ.zonotope_outer (Zonotope.ellipsoid_outer _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
