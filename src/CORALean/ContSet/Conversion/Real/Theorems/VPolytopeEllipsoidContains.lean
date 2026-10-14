module

public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A hull as an ellipsoid

Through the zonotope the hull's own box gives. A direct minimum-volume
enclosing ellipsoid of a vertex list is a separate piece of mathematics, and
this composition is not it.

Loses whatever the zonotope route loses on top of the box the hull already
loses to.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.ellipsoid_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.ellipsoid.construct :=
  subset_trans P.zonotope_contains (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
