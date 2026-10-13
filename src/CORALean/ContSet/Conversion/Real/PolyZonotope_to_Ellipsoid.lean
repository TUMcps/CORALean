module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A polynomial zonotope as an ellipsoid

Through the zonotope enclosure, then that zonotope's `√h` ball. A polynomial
zonotope's set is generally not even convex, so no ellipsoid is exact for it:
this is an enclosure with a precision knob rather than a conversion, and a
direct construction would be tighter.

Loses whatever both steps lose: the zonotope's own enclosure, then the
cube-to-ball inflation.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def PolyZonotope.ellipsoid (pZ : PolyZonotope (Vec ℝ n)) : Ellipsoid n :=
  pZ.zonotope.ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.ellipsoid_contains (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.construct ⊆ pZ.ellipsoid.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
