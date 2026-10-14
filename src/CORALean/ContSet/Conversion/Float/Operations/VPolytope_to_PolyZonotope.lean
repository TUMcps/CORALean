module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A hull as a polynomial zonotope, over a floating-point scalar — the construction

`VPolytope.polyZonotope` is the construction; `VPolytope_to_PolyZonotope` states and proves what it
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

def VPolytope.polyZonotope (P : VPolytope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  P.zonotope.polyZonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
