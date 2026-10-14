module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A halfspace description as an ellipsoid, over a floating-point scalar — the construction

`HPolytope.ellipsoid` is the construction; `HPolytope_to_Ellipsoid` states and proves what it
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

def HPolytope.ellipsoid {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  (HPolytope.zonotope up lo).ellipsoid σ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
