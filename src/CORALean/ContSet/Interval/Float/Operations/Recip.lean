module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.recip`, over a floating-point scalar

`1 ./ denominator`, the two reciprocals swapping. `divUp` and `divDown` ask for a positive
divisor, so a coordinate below `0` is negated first: for a positive box `[a, b]` the result is
`[1/b, 1/a]` rounded outward, and for a negative one `[-1/(-b), -1/(-a)]`. Which side a coordinate
lies on is decided by `ltStrict`, whose `true` certifies the strict inequality; the negative branch
is taken whenever the positive one is not certified, which is sound for a box the caller certifies
to avoid `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.recip (J : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i =>
    if ltStrict zero (J.inf i) then divDown one (J.sup i) else neg (divUp one (neg (J.sup i)))
  sup := fun i =>
    if ltStrict zero (J.inf i) then divUp one (J.inf i) else neg (divDown one (neg (J.inf i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
