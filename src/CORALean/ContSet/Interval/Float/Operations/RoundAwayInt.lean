import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

/-!
# `roundAwayInt`: MATLAB's `round` of an exact rational

The nearest integer, halves away from zero, as an integer: the computable counterpart of the exact
layer's `roundAway`, taken on the rational a scalar decodes to.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The nearest integer to `q`, halves away from zero. -/
def roundAwayInt (q : ℚ) : ℤ :=
  if 0 ≤ q then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
