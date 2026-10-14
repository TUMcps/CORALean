module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Volume
public import CORALean.ContSet.Interval.Float.Theorems.VolumeOuter
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.EllipsoidIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Ellipsoid.volume` bounds the volume

The checked half-widths make the interval hull hold the ellipsoid (`Ellipsoid.interval_contains`),
whose Lebesgue measure the rounded-up product bounds (`Interval.volume_le`). An upper bound only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.volume_le {E : Ellipsoid 𝕋 n} {s : Vec 𝕋 n} {v : 𝕋}
    (h : E.volume s = some v) :
    MeasureTheory.volume E.construct ≤ ENNReal.ofReal (toReal v) := by -- --- PROOF ---
  simp only [Ellipsoid.volume] at h
  split_ifs at h with hs
  simp only [Option.some.injEq] at h
  subst h
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at hs
  exact le_trans (MeasureTheory.measure_mono
    (Ellipsoid.interval_contains E s fun i => toReal_le_of_le (hs i)))
    (Interval.volume_le (E.interval s))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
