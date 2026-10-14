module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope

@[expose] public section

/-!
# A polynomial zonotope as its corners, over a floating-point scalar — the construction

`PolyZonotope.vPolytope` is the construction; `PolyZonotope_to_VPolytope` states and proves what it
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

def PolyZonotope.vPolytope (pZ : PolyZonotope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  pZ.zonotope.vPolytope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
