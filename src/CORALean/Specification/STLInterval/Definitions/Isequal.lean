module

public import CORALean.Specification.STLInterval.Definitions.IsWithinTol

@[expose] public section

/-!
# `isequal` of two STL intervals

`@stlInterval/isequal.m`: two empty intervals are equal, an empty and a nonempty one are not,
otherwise both bounds agree up to `tol` and both flags are the same.

## Inputs
* `tol` – tolerance

## Output
* the two intervals are equal up to the tolerance
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

def STLInterval.isequal (tol : ℝ) : STLInterval 𝕋 → STLInterval 𝕋 → Prop
  | .empty, .empty => True
  | .nonempty .., .empty => False
  | .empty, .nonempty .. => False
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    IsWithinTol tol (toReal l₁ : ℝ) (toReal l₂ : ℝ) ∧ IsWithinTol tol (toEReal u₁) (toEReal u₂) ∧
      lc₁ = lc₂ ∧ rc₁ = rc₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
