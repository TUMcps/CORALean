module

public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# `roundAwayInt`: MATLAB's `round` of an exact rational

The nearest integer, halves away from zero, as an integer: the computable counterpart of the exact
layer's `roundAway`, taken on the rational a scalar decodes to.

## Inputs
* `q` – exact rational

## Output
* nearest integer, halves away from zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The nearest integer to `q`, halves away from zero. -/
def roundAwayInt (q : ℚ) : ℤ :=
  if 0 ≤ q then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
