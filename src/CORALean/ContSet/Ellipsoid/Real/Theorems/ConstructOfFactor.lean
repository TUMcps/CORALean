module

public import CORALean.ContSet.Ellipsoid.Real.Operations.OfFactor
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqOfFactor

@[expose] public section

/-!
# The ellipsoid of a factored shape matrix is the image of the ball under the factor

`ellipsoid(F*F', q)` is `{q + F u | ‖u‖₂ ≤ 1}`, whatever the width of `F`: `construct_eq_of_factor`
at the factor the shape was built from.

## Inputs
* `F` – factor
* `q` – center

## Hypotheses
* none

## Conclusion
* the ellipsoid is the image of the unit ball under `F` about `q`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ellipsoid(F*F', q)` is the image of the unit ball under `F`, about `q`. -/
theorem Ellipsoid.construct_ofFactor (F : Mat ℝ n k) (q : Vec ℝ n) :
    (Ellipsoid.ofFactor F q).construct = {x | ∃ u : Vec ℝ k, ‖u‖₂ ≤ 1 ∧ x = q + F *ᵥ u} :=
  (Ellipsoid.ofFactor F q).construct_eq_of_factor F rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
