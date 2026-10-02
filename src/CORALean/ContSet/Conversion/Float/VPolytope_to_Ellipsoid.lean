import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Ellipsoid

/-!
# A hull as an ellipsoid, over a floating-point scalar

Through its zonotope, which is its box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.ellipsoid (P : VPolytope 𝕋 n) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  P.zonotope.ellipsoid σ


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.ellipsoid_contains (P : VPolytope 𝕋 n) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : (P.zonotope.h : ℝ) ≤ toReal (mulDown σ σ)) :
    P.construct ⊆ (P.ellipsoid σ).construct :=
  subset_trans P.zonotope_contains (P.zonotope.ellipsoid_contains σ hσ hh)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
