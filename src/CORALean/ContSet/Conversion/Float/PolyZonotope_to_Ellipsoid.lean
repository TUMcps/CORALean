import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Ellipsoid

/-!
# A polynomial zonotope as an ellipsoid, over a floating-point scalar

Through the zonotope enclosure, then that zonotope's `√h` ball, whose `σ` is proposed by
the caller and checked as in `Zonotope.ellipsoid`; here `h` counts the dependent and the
independent generators together.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def PolyZonotope.ellipsoid (pZ : PolyZonotope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  pZ.zonotope.ellipsoid σ


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.ellipsoid_contains (pZ : PolyZonotope (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : ((pZ.h + pZ.q : ℕ) : ℝ) ≤ toReal (mulDown σ σ)) :
    pZ.construct ⊆ (pZ.ellipsoid σ).construct :=
  subset_trans pZ.zonotope_contains (pZ.zonotope.ellipsoid_contains σ hσ hh)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
