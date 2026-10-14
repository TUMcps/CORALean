module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A halfspace description as a polynomial zonotope, over a floating-point scalar — the construction

`HPolytope.polyZonotope` is the construction; `HPolytope_to_PolyZonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.polyZonotope (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : PolyZonotope (Vec 𝕋 n) :=
  (HPolytope.zonotope up lo).polyZonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
