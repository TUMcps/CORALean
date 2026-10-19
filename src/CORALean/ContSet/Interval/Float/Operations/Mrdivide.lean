module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.mrdivide`, over a floating-point scalar

A scalar denominator `d`: each endpoint divided by `d` and rounded outward. `divUp` and
`divDown` ask for a positive divisor, so a negative `d` negates both the box and `d`
(`x / d = (-x) / (-d)`), which swaps the endpoints. The branch is `ltStrict`'s, as in `recip`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.mrdivide (numerator : Interval (Vec 𝕋 n)) (d : 𝕋) : Interval (Vec 𝕋 n) where
  inf := fun i =>
    if ltStrict zero d then divDown (numerator.inf i) d
    else divDown (neg (numerator.sup i)) (neg d)
  sup := fun i =>
    if ltStrict zero d then divUp (numerator.sup i) d
    else divUp (neg (numerator.inf i)) (neg d)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
