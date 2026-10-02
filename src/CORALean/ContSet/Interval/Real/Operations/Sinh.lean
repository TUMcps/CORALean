import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.Complex.Trigonometric

/-!
# `Interval.sinh`

CORA's `@interval/sinh`: the hyperbolic sine is strictly increasing and continuous on all of `ℝ`,
so it acts on the two bounds, coordinate by coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.sinh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.sinh (I.inf i)
  sup := fun i => Real.sinh (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
