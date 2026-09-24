import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Real.Operations.MulLo

/-!
# `Interval.mulLo` never exceeds the exact corner hull

Each of the four corner products rounds down, and `minimum` is exact, so the
float hull sits at or under the real one taken at the same four corners.
Public rather than `aux_`: `MatMulOuter` and `MtimesIntervalMatOuter` both
need it, not only `MulBetweenCorners`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mulLo_le (a b c d : 𝕋) :
    toReal (Interval.mulLo a b c d)
      ≤ Real.Interval.mulLo (toReal a) (toReal b) (toReal c) (toReal d) := by
  rw [Interval.mulLo, Real.Interval.mulLo, toReal_minimum, toReal_minimum, toReal_minimum]
  exact min_le_min (min_le_min (mulDown_le_mul a c) (mulDown_le_mul a d))
    (min_le_min (mulDown_le_mul b c) (mulDown_le_mul b d))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
