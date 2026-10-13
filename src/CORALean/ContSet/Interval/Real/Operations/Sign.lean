import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Data.Real.Sign

/-!
# `Interval.sign`

CORA's `@interval/sign`: `interval(sign(I.inf), sign(I.sup))`, the hull of the image.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.sign (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.sign (I.inf i)
  sup := fun i => Real.sign (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
