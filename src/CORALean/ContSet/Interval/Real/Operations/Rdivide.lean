module

public import CORALean.ContSet.Interval.Real.Operations.Recip
public import CORALean.ContSet.Interval.Real.Operations.Times

@[expose] public section

/-!
# `Interval.rdivide`

CORA's `@interval/rdivide` at two intervals: `y = 1 ./ denominator; res = numerator .* y`. A
quotient of independent boxes is the product of the numerator with the reciprocal box, which
is why this is `times` after `recip`.

## Inputs
* `numerator` – box of the numerators
* `denominator` – box of the denominators

## Output
* entrywise quotient box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
