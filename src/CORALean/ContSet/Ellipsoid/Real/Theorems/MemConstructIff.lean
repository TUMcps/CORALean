module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt

@[expose] public section

/-!
# Membership through the square root

`x ∈ E` iff `x = q + G u` for some `‖u‖₂ ≤ 1`: `Theorems/ConstructEqSqrt`, read pointwise, so that
a point is shown in or taken out of the ellipsoid by its coefficient `u`.

## Inputs
* `E` – ellipsoid
* `x` – point

## Hypotheses
* none

## Conclusion
* `x ∈ E` iff `x = q + G u` with `‖u‖ ≤ 1`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x ∈ E` iff `x = q + G u` with `‖u‖₂ ≤ 1`. -/
theorem Ellipsoid.mem_construct_iff {E : Ellipsoid n} {x : Vec ℝ n} :
    x ∈ E.construct ↔ ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧ x = E.q + E.G *ᵥ u := by
  rw [E.construct_eq_sqrt]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
