import CORALean.ContSet.Interval.Float.Theorems.VolumeNominalLe

/-!
# `Interval.volume` bounds the Lebesgue volume

The denoted box's Lebesgue volume is at most the stored bound, `ofReal`-read.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.volume_le (I : Interval (Vec 𝕋 n)) :
    MeasureTheory.volume I.construct ≤ ENNReal.ofReal (toReal I.volume) := by
  have h : I.construct = I.nominal.construct := rfl
  rw [h, Real.Interval.volume_eq]
  exact I.volume_nominal_le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
