module

public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

@[expose] public section

/-!
# A constrained zonotope as a box, over a floating-point scalar — the construction

`ConZonotope.interval` is the construction; `ConZonotope_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.interval (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  cZ.zonotope.interval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
