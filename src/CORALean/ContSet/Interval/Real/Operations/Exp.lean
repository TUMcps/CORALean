import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.Complex.Exponential

/-!
# `Interval.exp`

CORA's `@interval/exp`: the exponential is increasing, so it acts on the two bounds, coordinate by
coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.exp (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.exp (I.inf i)
  sup := fun i => Real.exp (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
