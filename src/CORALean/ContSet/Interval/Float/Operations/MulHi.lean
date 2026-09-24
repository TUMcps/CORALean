import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.mulHi`, over a floating-point scalar

The greatest of the four corner products of `[a, b]` and `[c, d]`, each corner
rounded up before the four are compared: `maximum` is exact, so only the four
products themselves cost a rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


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
