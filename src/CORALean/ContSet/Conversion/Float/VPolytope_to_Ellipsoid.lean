module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_Ellipsoid

@[expose] public section

/-!
# A hull as an ellipsoid, over a floating-point scalar

Through its zonotope, which is its box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.ellipsoid_contains (P : VPolytope (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : (P.zonotope.h : ℝ) ≤ toReal (mulDown σ σ)) :
    P.construct ⊆ (P.ellipsoid σ).construct :=
  subset_trans P.zonotope_contains (P.zonotope.ellipsoid_contains σ hσ hh)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
