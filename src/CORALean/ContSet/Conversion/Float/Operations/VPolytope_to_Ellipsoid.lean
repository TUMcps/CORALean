module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A hull as an ellipsoid, over a floating-point scalar — the construction

`VPolytope.ellipsoid` is the construction; `VPolytope_to_Ellipsoid` states and proves what it
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

def VPolytope.ellipsoid (P : VPolytope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  P.zonotope.ellipsoid σ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
