module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConPolyZono

@[expose] public section

/-!
# A halfspace description as a constrained polynomial zonotope, over a floating-point scalar

Through the polynomial zonotope; the constraint-free embedding is exact.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.conPolyZono_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conPolyZono up lo).construct :=
  subset_trans (HPolytope.polyZonotope_contains up lo) (PolyZonotope.conPolyZono_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
