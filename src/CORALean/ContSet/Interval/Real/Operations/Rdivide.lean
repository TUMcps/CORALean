import CORALean.ContSet.Interval.Real.Operations.Recip
import CORALean.ContSet.Interval.Real.Operations.Times

/-!
# `Interval.rdivide`

CORA's `@interval/rdivide` at two intervals: `y = 1 ./ denominator; res = numerator .* y`. A
quotient of independent boxes is the product of the numerator with the reciprocal box, which
is why this is `times` after `recip`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.rdivide (numerator denominator : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) :=
  let y := denominator.recip
  numerator.times y

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
