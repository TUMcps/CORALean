module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A halfspace description as a polynomial zonotope, over a floating-point scalar

Through its box's zonotope, whose polynomial-zonotope reading is exact.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}

def HPolytope.polyZonotope (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : PolyZonotope (Vec 𝕋 n) :=
  (HPolytope.zonotope up lo).polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.polyZonotope_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.polyZonotope up lo).construct :=
  subset_trans (HPolytope.zonotope_contains up lo) (Zonotope.polyZonotope_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
