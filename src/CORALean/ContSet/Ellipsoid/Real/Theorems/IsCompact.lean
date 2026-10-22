module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqImage
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ContinuousAffine

@[expose] public section

/-!
# An ellipsoid is compact

The Euclidean unit ball is compact — closed because `‖·‖₂` is continuous, and
inside the supremum-norm ball the ambient type carries because no coordinate
exceeds the whole — and the affine map onto the ellipsoid is continuous.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* `E` is compact
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The continuous image of a closed ball that is compact where it is stated,
`EuclideanSpace ℝ (Fin n)` being finite-dimensional. -/
theorem _root_.CORALean.aux_isCompact_unitBall₂ : IsCompact (unitBall₂ n) := by
  rw [unitBall₂_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isCompact_construct (E : Ellipsoid n) : IsCompact E.construct := by
  rw [E.construct_eq_image]
  exact aux_isCompact_unitBall₂.image E.continuous_affine

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
