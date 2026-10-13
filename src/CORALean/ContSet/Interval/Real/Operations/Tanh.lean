import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.Complex.Trigonometric

/-!
# `Interval.tanh`

CORA's `@interval/tanh`: the hyperbolic tangent is strictly increasing and continuous on all of
`ℝ`, so it acts on the two bounds, coordinate by coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.tanh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.tanh (I.inf i)
  sup := fun i => Real.tanh (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
