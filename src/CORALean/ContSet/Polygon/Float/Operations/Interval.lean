import CORALean.ContSet.Polygon.Float.Operations.IntervalOfList

/-!
# `Polygon.interval`, over a floating-point scalar

The hull of the pieces' boxes (`Interval.or`), the empty box for no pieces.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box holding every piece. -/
def Polygon.interval (P : Polygon 𝕋) : Interval (Vec 𝕋 2) :=
  Polygon.intervalOfList P.sets

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
