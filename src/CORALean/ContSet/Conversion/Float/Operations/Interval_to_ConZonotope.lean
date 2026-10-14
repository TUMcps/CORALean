module

public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A box as a constrained zonotope, over a floating-point scalar — the construction

`Interval.conZonotope` is the construction; `Interval_to_ConZonotope` states and proves what it
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

def Interval.conZonotope (I : Interval (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  I.zonotope.conZonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
