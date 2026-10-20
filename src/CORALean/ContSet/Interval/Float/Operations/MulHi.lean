module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.mulHi`, over a floating-point scalar

The greatest of the four corner products of `[a, b]` and `[c, d]`, each corner
rounded up before the four are compared: `maximum` is exact, so only the four
products themselves cost a rounding.

## Inputs
* `a` – lower end of the first factor
* `b` – upper end of the first factor
* `c` – lower end of the second factor
* `d` – upper end of the second factor

## Output
* upper end of the interval product of `[a, b]` and `[c, d]`
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The greatest of the four corner products of `[a, b]` and `[c, d]`, each
corner rounded up. -/
def Interval.mulHi (a b c d : 𝕋) : 𝕋 :=
  maximum (maximum (mulUp a c) (mulUp a d)) (maximum (mulUp b c) (mulUp b d))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
