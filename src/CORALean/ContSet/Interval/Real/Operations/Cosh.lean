import CORALean.ContSet.Interval.Real.Operations.CoshLo
import CORALean.ContSet.Interval.Real.Operations.CoshHi

/-!
# `Interval.cosh`

CORA's `@interval/cosh`, coordinate by coordinate: the three cases (range left of `0`, right of
`0`, or containing `0`) are `coshLo` and `coshHi`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.cosh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Interval.coshLo (I.inf i) (I.sup i)
  sup := fun i => Interval.coshHi (I.inf i) (I.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
