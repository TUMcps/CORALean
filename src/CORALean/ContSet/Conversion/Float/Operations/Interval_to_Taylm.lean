module

public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Taylm

@[expose] public section

/-!
# A box as an array of Taylor models, over a floating-point scalar — the construction

`Interval.taylm` is the construction; `Interval_to_Taylm` states and proves what it guarantees.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.taylm (I : Interval (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 n :=
  I.zonotope.taylm N

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
