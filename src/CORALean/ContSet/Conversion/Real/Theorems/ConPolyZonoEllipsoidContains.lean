module

public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeEllipsoidContains

@[expose] public section

/-!
# A constrained polynomial zonotope as an ellipsoid

Through `ConPolyZono.polyZonotope`, then that polynomial zonotope's own ball. Precision is lost
twice over: the constraints go first, freeing every factor the equalities were confining, and then
the sharing goes, at `PolyZonotope.zonotope`, before the cube-to-ball inflation. No loss is
recovered by another. A direct ellipsoid from a constrained polynomial zonotope is a separate piece
of mathematics, and no tighter enclosure is attempted here.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its ellipsoid
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.ellipsoid_contains (cPZ : ConPolyZono (Vec ℝ n)) :
    cPZ.construct ⊆ cPZ.ellipsoid.construct :=
  subset_trans cPZ.polyZonotope_contains (PolyZonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
