module

public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A constrained zonotope as an ellipsoid

Through the plain zonotope the constraints are dropped for, then that
zonotope's `√h` ball. A direct enclosure that used the constraints instead of
throwing them away is a separate piece of mathematics.

Loses whatever both steps lose: the constraints, then the cube-to-ball
inflation.

## Inputs
* `cZ` – constrained zonotope

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

theorem ConZonotope.ellipsoid_contains (cZ : ConZonotope (Vec ℝ n)) :
    cZ.construct ⊆ cZ.ellipsoid.construct :=
  subset_trans cZ.zonotope_contains (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
