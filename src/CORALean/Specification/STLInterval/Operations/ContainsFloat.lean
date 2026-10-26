module

public import CORALean.Specification.STLInterval.Instances
public import CORALean.Specification.STLInterval.Operations.WithinTolFloat
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `contains_` of two intervals over a float scalar

`@stlInterval/contains_.m` for an interval in an interval, with time stamps in `𝕋`: the empty
interval contains only the empty one, a nonempty one contains the empty one, and otherwise each end
of the second is inside the first or within the tolerance of it (`withinTolFloat`, decided
exactly) with compatible closedness. It decides `contains_` of the intervals
(`containsFloat_iff`).

## Inputs
* `tol` – tolerance

## Output
* whether the first interval contains the second up to the tolerance
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contains_(I,J,tol)` of two intervals, decided exactly on the bounds. -/
def STLInterval.containsFloat (tol : 𝕋) : STLInterval 𝕋 → STLInterval 𝕋 → Bool
  | .empty, .empty => true
  | .empty, .nonempty .. => false
  | .nonempty .., .empty => true
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let upperIncluded := decide (STLInterval.toEReal u₁ > STLInterval.toEReal u₂) ||
      (STLInterval.withinTolFloat tol u₁ u₂ && (rc₁ || !rc₂))
    let lowerIncluded := decide (toReal l₁ < toReal l₂) ||
      (STLInterval.withinTolFloat tol l₁ l₂ && (lc₁ || !lc₂))
    lowerIncluded && upperIncluded

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
