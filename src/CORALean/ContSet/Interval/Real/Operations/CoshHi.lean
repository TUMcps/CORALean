import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.Complex.Trigonometric

/-!
# `Interval.coshHi`

The upper bound of `cosh` on one coordinate `[lb, ub]`, from CORA's `@interval/cosh`: `cosh lb` if
the range lies at or left of `0`, `cosh ub` if at or right of it, and `cosh` at the end of larger
absolute value if `0` lies inside.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.coshHi (lb ub : ℝ) : ℝ :=
  if ub ≤ 0 then Real.cosh lb else if 0 ≤ lb then Real.cosh ub
  else Real.cosh (max |lb| |ub|)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
