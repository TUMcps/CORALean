import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_SpectraShadow

/-!
# A box as a spectrahedral shadow, over a floating-point scalar

Through the zonotope. The generators absorb the centre's rounding there, and the
inequality is the exact diagonal one here, so nothing further is paid.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Interval.spectraShadow (I : Interval (Vec 𝕋 n)) : SpectraShadow 𝕋 n :=
  I.zonotope.spectraShadow


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.spectraShadow_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.spectraShadow.construct :=
  subset_trans I.zonotope_contains (Zonotope.spectraShadow_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
