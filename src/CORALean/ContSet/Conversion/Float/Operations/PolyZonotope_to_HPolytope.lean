module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope

@[expose] public section

/-!
# A polynomial zonotope as halfspaces, over a floating-point scalar — the construction

`PolyZonotope.hPolytope` is the construction; `PolyZonotope_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.hPolytope (pZ : PolyZonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  pZ.zonotope.hPolytope Aq

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
