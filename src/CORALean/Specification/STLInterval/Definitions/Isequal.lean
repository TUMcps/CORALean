module

public import CORALean.Specification.STLInterval.Definitions.WithinTol

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


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.isequal (tol : ℝ) : STLInterval → STLInterval → Prop
  | .empty, .empty => True
  | .nonempty .., .empty => False
  | .empty, .nonempty .. => False
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ _ =>
    withinTol tol l₁ l₂ ∧ withinTol tol u₁ u₂ ∧ lc₁ = lc₂ ∧ rc₁ = rc₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
