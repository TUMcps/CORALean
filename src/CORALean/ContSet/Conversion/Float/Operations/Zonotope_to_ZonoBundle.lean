module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

@[expose] public section

/-!
# A zonotope as a bundle of one, over a floating-point scalar — the construction

`Zonotope.zonoBundle` is the construction; `Zonotope_to_ZonoBundle` states and proves what it
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

def Zonotope.zonoBundle (Z : Zonotope (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) := ⟨1, fun _ => Z⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
