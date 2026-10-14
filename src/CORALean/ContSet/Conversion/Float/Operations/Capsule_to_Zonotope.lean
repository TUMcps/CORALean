module

public import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

@[expose] public section

/-!
# A capsule as a zonotope, over a floating-point scalar — the construction

`Capsule.zonotope` is the construction; `Capsule_to_Zonotope` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.zonotope (C : Capsule 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  C.interval.zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
