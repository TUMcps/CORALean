module

public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# A constrained zonotope as a bundle of one, over a floating-point scalar — the construction

`ConZonotope.zonoBundle` is the construction; `ConZonotope_to_ZonoBundle` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.zonoBundle (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) :=
  cZ.zonotope.zonoBundle

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
