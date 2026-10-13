module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.mulLo`, over a floating-point scalar

The least of the four corner products of `[a, b]` and `[c, d]`, each corner
rounded down before the four are compared: `minimum` is exact, so only the four
products themselves cost a rounding.
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

/-- The least of the four corner products of `[a, b]` and `[c, d]`, each corner
rounded down. -/
def Interval.mulLo (a b c d : 𝕋) : 𝕋 :=
  minimum (minimum (mulDown a c) (mulDown a d)) (minimum (mulDown b c) (mulDown b d))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
