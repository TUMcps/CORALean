import CORALean.ContSet.Interval.Float.Operations.Recip
import CORALean.ContSet.Interval.Float.Operations.Times

/-!
# `Interval.rdivide`, over a floating-point scalar

`y = 1 ./ denominator; res = numerator .* y`: `times` at the outward-rounded reciprocal box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.rdivide (numerator denominator : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  let y := denominator.recip
  numerator.times y

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
