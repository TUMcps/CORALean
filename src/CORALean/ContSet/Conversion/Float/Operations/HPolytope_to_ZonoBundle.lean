module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# A halfspace description as a bundle of one, over a floating-point scalar — the construction

`HPolytope.zonoBundle` is the construction; `HPolytope_to_ZonoBundle` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.zonoBundle (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ZonoBundle (Vec 𝕋 n) :=
  (HPolytope.zonotope up lo).zonoBundle

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
