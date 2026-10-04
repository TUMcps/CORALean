import CORALean.ContSet.Polygon.Float.Operations.Volume
import CORALean.ContSet.Polygon.Float.Theorems.IntervalContains
import CORALean.ContSet.Interval.Float.Theorems.VolumeOuter

/-!
# `Polygon.volume` bounds the area

The region lies in its interval hull (`Polygon.interval_contains`), whose Lebesgue measure the
rounded-up product bounds (`Interval.volume_le`). An upper bound only.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.volume_le (P : Polygon 𝕋) :
    MeasureTheory.volume (ContSet.construct P) ≤ ENNReal.ofReal (toReal (Polygon.volume P)) :=
  le_trans (MeasureTheory.measure_mono (Polygon.interval_contains P))
    (Interval.volume_le (Polygon.interval P))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
