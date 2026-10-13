import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.abs`

CORA's `@interval/abs`: the lower bound is `0` when the interval contains `0`, else the smaller
absolute value of its ends; the upper bound is the larger one. In maxima: `max 0 (inf, -sup)` and
`max (-inf, sup)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.abs (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => max 0 (max (I.inf i) (-I.sup i))
  sup := fun i => max (-I.inf i) (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
