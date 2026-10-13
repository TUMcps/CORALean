module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.recip`

CORA's `1 ./ denominator` for an interval denominator, `res.inf = 1 ./ sup`, `res.sup = 1 ./ inf`
(the two reciprocals swap). It is meaningful away from `0`; CORA's `-Inf`/`+Inf`/`NaN` cases for a
denominator containing `0` have no counterpart in `ℝ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.recip (J : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => (J.sup i)⁻¹
  sup := fun i => (J.inf i)⁻¹

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
