import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# `Interval.asin`

CORA's `@interval/asin`: the arcsine is strictly increasing on `[-1, 1]`, so it acts on the two
bounds, coordinate by coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.asin (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.arcsin (I.inf i)
  sup := fun i => Real.arcsin (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
