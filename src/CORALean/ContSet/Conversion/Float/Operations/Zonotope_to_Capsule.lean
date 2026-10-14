module

public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_Capsule

@[expose] public section

/-!
# A zonotope as a capsule, over a floating-point scalar — the construction

`Zonotope.capsule` is the construction; `Zonotope_to_Capsule` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.capsule (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) : Capsule 𝕋 n :=
  Z.interval.capsule k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
