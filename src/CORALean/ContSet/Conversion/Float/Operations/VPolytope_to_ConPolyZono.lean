module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A hull as a constrained polynomial zonotope, over a floating-point scalar — the construction

`VPolytope.conPolyZono` is the construction; `VPolytope_to_ConPolyZono` states and proves what it
guarantees.
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

def VPolytope.conPolyZono (P : VPolytope (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  P.polyZonotope.conPolyZono

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
