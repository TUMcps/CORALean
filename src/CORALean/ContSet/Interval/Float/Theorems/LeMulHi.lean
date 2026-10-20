module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.mulHi` never falls under the exact corner hull

Each of the four corner products rounds up, and `maximum` is exact, so the
float hull sits at or over the real one taken at the same four corners.
Public rather than `aux_`, for the reason `MulLoLe` states.

## Inputs
* `a` – lower end of the first factor
* `b` – upper end of the first factor
* `c` – lower end of the second factor
* `d` – upper end of the second factor

## Hypotheses
* none

## Conclusion
* the exact upper product end is at most the float one
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.le_mulHi (a b c d : 𝕋) :
    Real.Interval.mulHi (toReal a) (toReal b) (toReal c) (toReal d)
      ≤ toReal (Interval.mulHi a b c d) := by
  rw [Interval.mulHi, Real.Interval.mulHi, toReal_maximum, toReal_maximum, toReal_maximum]
  exact max_le_max (max_le_max (mul_le_mulUp a c) (mul_le_mulUp a d))
    (max_le_max (mul_le_mulUp b c) (mul_le_mulUp b d))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
