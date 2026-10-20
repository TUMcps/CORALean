module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# An ellipsoid as its corners

Through the zonotope, then that zonotope's `2^h` sign corners. A tight vertex
enclosure of an ellipsoid is its own fitting problem, not this composition, and
CORA leaves that choice to the caller too.

Loses whatever the zonotope step lost and nothing further, the corner step
being exact.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* ellipsoid is contained in its vertex polytope
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.vPolytope_contains (E : Ellipsoid n) : E.construct ⊆ E.vPolytope.construct :=
  subset_trans E.zonotope_contains (Zonotope.vPolytope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
