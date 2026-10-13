import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `Interval.log`

CORA's `@interval/log`: the logarithm is increasing on `(0, ∞)`, so it acts on the two bounds,
coordinate by coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.log (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.log (I.inf i)
  sup := fun i => Real.log (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
