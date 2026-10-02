import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# `Interval.atanh`

CORA's `@interval/atanh`:
the inverse hyperbolic tangent is increasing on `(-1, 1)`, so it acts on the two
bounds, coordinate by coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.atanh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.artanh (I.inf i)
  sup := fun i => Real.artanh (I.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
