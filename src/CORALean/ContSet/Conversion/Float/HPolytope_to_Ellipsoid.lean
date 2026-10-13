module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A halfspace description as an ellipsoid, over a floating-point scalar

Through its zonotope, which is its box, from the same certificates.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def HPolytope.ellipsoid {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  (HPolytope.zonotope up lo).ellipsoid σ


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ellipsoid_contains {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : ((HPolytope.zonotope up lo).h : ℝ) ≤ toReal (mulDown σ σ)) :
    P.construct ⊆ (HPolytope.ellipsoid up lo σ).construct :=
  subset_trans (HPolytope.zonotope_contains up lo)
    ((HPolytope.zonotope up lo).ellipsoid_contains σ hσ hh)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
