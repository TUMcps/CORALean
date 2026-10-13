import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# `Interval.acos`

CORA's `@interval/acos`: the arccosine is strictly decreasing on `[-1, 1]`, so the corners swap,
so it acts on the two bounds, coordinate by coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.acos (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.arccos (I.sup i)
  sup := fun i => Real.arccos (I.inf i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
