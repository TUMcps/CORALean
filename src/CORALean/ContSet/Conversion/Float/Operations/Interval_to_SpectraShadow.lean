module

public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A box as a spectrahedral shadow, over a floating-point scalar — the construction

`Interval.spectraShadow` is the construction; `Interval_to_SpectraShadow` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.spectraShadow (I : Interval (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  I.zonotope.spectraShadow

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
