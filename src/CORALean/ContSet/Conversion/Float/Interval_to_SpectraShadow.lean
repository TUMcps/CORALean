module

public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_SpectraShadow

@[expose] public section

/-!
# A box as a spectrahedral shadow, over a floating-point scalar

Through the zonotope. The generators absorb the centre's rounding there, and the
inequality is the exact diagonal one here, so nothing further is paid.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.spectraShadow_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.spectraShadow.construct :=
  subset_trans I.zonotope_contains (Zonotope.spectraShadow_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
