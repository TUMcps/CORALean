module

public import CORALean.ContSet.Polygon.Float.Operations.Volume
public import CORALean.ContSet.Polygon.Float.Theorems.IntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.VolumeOuter
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Polygon.volume` bounds the area

The region lies in its interval hull (`Polygon.interval_contains`), whose Lebesgue measure the
rounded-up product bounds (`Interval.volume_le`). An upper bound only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
