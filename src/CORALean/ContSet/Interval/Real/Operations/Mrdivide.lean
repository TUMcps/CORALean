import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.mrdivide`

CORA's `@interval/mrdivide` with a scalar denominator, which calls `rdivide` at a number `d`:
`res.inf = min(inf ./ d, sup ./ d)` and `res.sup = max(inf ./ d, sup ./ d)`, the two
quotients swapping when `d` is negative. CORA's `±Inf` at `d = 0` has no counterpart in `ℝ`,
so `d ≠ 0` is an assumption of the exactness theorem. A scalar interval denominator goes through
`Interval.rdivide`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.mrdivide (numerator : Interval (Vec ℝ n)) (d : ℝ) :
    Interval (Vec ℝ n) where
  inf := fun i => min (numerator.inf i / d) (numerator.sup i / d)
  sup := fun i => max (numerator.inf i / d) (numerator.sup i / d)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
