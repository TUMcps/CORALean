module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A polynomial zonotope as an ellipsoid, over a floating-point scalar — the construction

`PolyZonotope.ellipsoid` is the construction; `PolyZonotope_to_Ellipsoid` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.ellipsoid (pZ : PolyZonotope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  pZ.zonotope.ellipsoid σ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
