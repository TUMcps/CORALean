import CORALean.ContSet.Interval.Real.Interval

/-!
# `roundAway`

CORA's `@interval/round` at its default of zero digits: MATLAB's `round` sends halves away from
zero, unlike Mathlib's `round`, which sends them up, so the function is spelled out. Only the
default `N = 0` is covered.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- MATLAB's `round`: to the nearest integer, halves away from zero. -/
noncomputable def roundAway (x : ℝ) : ℝ :=
  if 0 ≤ x then (⌊x + 1 / 2⌋ : ℝ) else -(⌊-x + 1 / 2⌋ : ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
