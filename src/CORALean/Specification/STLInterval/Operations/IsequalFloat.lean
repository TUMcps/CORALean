module

public import CORALean.Specification.STLInterval.Operations.WithinTolFloat
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `isequal` of two intervals over a float scalar

`@stlInterval/isequal.m` with time stamps in `𝕋`: both empty, or both nonempty with the bounds
within the tolerance (`withinTolFloat`, decided exactly) and the same closedness. It decides
`isequal` of the intervals (`isequalFloat_iff`).

## Inputs
* `tol` – tolerance

## Output
* whether the two intervals are equal up to the tolerance
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `isequal(I,J,tol)`, decided exactly on the bounds. -/
def STLInterval.isequalFloat (tol : 𝕋) : STLInterval 𝕋 → STLInterval 𝕋 → Bool
  | .empty, .empty => true
  | .nonempty .., .empty => false
  | .empty, .nonempty .. => false
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    STLInterval.withinTolFloat tol l₁ l₂ && STLInterval.withinTolFloat tol u₁ u₂ &&
      lc₁ == lc₂ && rc₁ == rc₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
