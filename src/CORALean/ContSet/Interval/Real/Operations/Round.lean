import CORALean.ContSet.Interval.Real.Operations.RoundAway

/-!
# `Interval.round`

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

noncomputable def Interval.round (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => roundAway (I.inf i)
  sup := fun i => roundAway (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
