module

public import CORALean.ContSet.Conversion.Float.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A spectrahedral shadow as a constrained zonotope, over a floating-point scalar — the construction

`SpectraShadow.conZonotope` is the construction; `SpectraShadow_to_ConZonotope` states and proves
what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.conZonotope (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (ConZonotope 𝕋 (Vec 𝕋 n)) :=
  (S.zonotope Yup Ylo).map Zonotope.conZonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
