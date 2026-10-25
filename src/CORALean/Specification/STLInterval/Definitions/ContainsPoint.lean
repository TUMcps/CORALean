module

public import CORALean.Specification.STLInterval.Definitions.IsWithinTol

@[expose] public section

/-!
# `contains_` of a point

`@stlInterval/contains_.m`, the numeric branch: strictly between the bounds, or at a closed bound
(up to `tol`). The empty interval contains nothing.

## Inputs
* `tol` – tolerance

## Output
* the interval contains the time up to the tolerance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.containsPoint (tol : ℝ) : STLInterval 𝕋 → ℝ → Prop
  | .empty, _ => False
  | .nonempty l u lc rc _ _ _, t =>
    (((toReal l : ℝ) : EReal) < t ∧ (t : EReal) < toEReal u) ∨
      (lc = true ∧ IsWithinTol tol (toReal l : ℝ) t) ∨
      (rc = true ∧ IsWithinTol tol (toEReal u) t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
