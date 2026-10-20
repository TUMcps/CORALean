module

public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A halfspace description as an ellipsoid

Through the zonotope the box gives. A direct minimum-volume enclosing
ellipsoid is a separate piece of mathematics; CORA computes one for a
halfspace description and this composition is not it.

Loses whatever the zonotope route loses on top of the box's own `2n` linear
programs.

## Inputs
* `up` – certified upper bound per coordinate
* `lo` – certified lower bound per coordinate

## Hypotheses
* none

## Conclusion
* polytope is contained in its ellipsoid
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ellipsoid_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.ellipsoid up lo).construct :=
  subset_trans (HPolytope.zonotope_contains up lo) (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
