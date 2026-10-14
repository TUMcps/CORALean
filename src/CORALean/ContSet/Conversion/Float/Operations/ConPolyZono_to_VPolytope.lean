module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_VPolytope

@[expose] public section

/-!
# A constrained polynomial zonotope as its corners, over a floating-point scalar — the construction

`ConPolyZono.vPolytope` is the construction; `ConPolyZono_to_VPolytope` states and proves what it
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

def ConPolyZono.vPolytope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  cPZ.zonotope.vPolytope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
