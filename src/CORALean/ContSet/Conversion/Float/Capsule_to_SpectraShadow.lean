module

public import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_SpectraShadow

@[expose] public section

/-!
# A capsule as a spectrahedral shadow, over a floating-point scalar

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion, as over ℝ: the capsule is first replaced by its axis-aligned box,
which loses the rounded ends and the slant of the segment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Capsule.spectraShadow (C : Capsule 𝕋 n) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  C.interval.spectraShadow


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.spectraShadow_contains (C : Capsule 𝕋 n) :
    C.construct ⊆ C.spectraShadow.construct :=
  subset_trans C.interval_contains (Interval.spectraShadow_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
