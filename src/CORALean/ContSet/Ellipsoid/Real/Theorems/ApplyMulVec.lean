module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic

@[expose] public section

/-!
# A functional at a generator-space image is a dot product with its pullback

The generator matrix carries the unit ball onto the ellipsoid; the functional reads the image
through the transpose.

## Inputs
* `E` – ellipsoid
* `c` – linear functional
* `u` – point of generator space

## Hypotheses
* none

## Conclusion
* the functional at the image equals the dot product of the pullback with the point
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A functional applied to a generator-space image is the dot product with its pullback -/
theorem Ellipsoid.apply_mulVec (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) (u : Vec ℝ n) :
    c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := by
  rw [apply_eq_dotProduct, dotProduct_mulVec, Ellipsoid.pullback, mulVec_transpose]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
