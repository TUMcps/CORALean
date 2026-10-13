module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.Global.Float.IntRound

@[expose] public section

/-!
# `Taylm.bernsteinStep`

Term `i` of `bernsteinEntry`, `C(j, i) / C(N, i) · (C(e, i) 2ⁱ (-1)^(e - i))`, between two floats:
the ratio from `divDown` of the rounded-down numerator by the rounded-up denominator, and `divUp`
of the rounded-up numerator by the rounded-down denominator when that is at least one, else by
the bound `1` (`C(j, i) ≤ C(N, i)`); the signed integer from its directed roundings;
the corner products. Zero for `i > j`, where `C(j, i) = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.bernsteinStep (N e j i : ℕ) : 𝕋 × 𝕋 :=
  if i ≤ j then
    -- the ratio, then the signed integer
    let rLo : 𝕋 := divDown (intDown (j.choose i : ℤ)) (intUp (N.choose i : ℤ))
    let rHi : 𝕋 := if le (one : 𝕋) (intDown (N.choose i : ℤ)) then
      divUp (intUp (j.choose i : ℤ)) (intDown (N.choose i : ℤ)) else one
    let c : ℤ := (e.choose i : ℤ) * 2 ^ i * (-1) ^ (e - i)
    (Interval.mulLo rLo rHi (intDown c) (intUp c), Interval.mulHi rLo rHi (intDown c) (intUp c))
  else (zero, zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
