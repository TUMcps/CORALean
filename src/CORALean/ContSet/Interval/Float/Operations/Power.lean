import CORALean.ContSet.Interval.Float.Operations.PowHi
import CORALean.ContSet.Interval.Float.Operations.PowLo

/-!
# `Interval.power`, over a floating-point scalar

`base .^ k` for a nonnegative integer exponent: per coordinate the hull of the two bounds
`powLo`/`powHi` at the corners. For an even `k ≠ 0` the lower bound is `0` unless `le` certifies
that the box lies on one side of `0`, where the hull of the corners is the lower bound, as in CORA.
`0` is always a lower bound of an even power, so the uncertified case is sound, and exactly
CORA's value for a box crossing `0`. Negative and non-integer exponents are not covered.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.power (I : Interval (Vec 𝕋 n)) (k : ℕ) : Interval (Vec 𝕋 n) where
  inf := fun i =>
    if k % 2 = 0 ∧ k ≠ 0 ∧ (le zero (I.inf i) || le (I.sup i) zero) = false then zero
    else minimum (Interval.powLo (I.inf i) k) (Interval.powLo (I.sup i) k)
  sup := fun i => maximum (Interval.powHi (I.inf i) k) (Interval.powHi (I.sup i) k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
