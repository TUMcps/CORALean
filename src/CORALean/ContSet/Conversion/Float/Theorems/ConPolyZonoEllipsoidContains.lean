module

public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalEllipsoidContains

@[expose] public section

/-!
# A constrained polynomial zonotope as an ellipsoid, over a floating-point scalar

Through its polynomial zonotope, as over ℝ; `σ` is checked against the generator count
of that polynomial zonotope's zonotope.
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

theorem ConPolyZono.ellipsoid_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : ((cPZ.polyZonotope.h + cPZ.polyZonotope.q : ℕ) : ℝ) ≤ toReal (mulDown σ σ)) :
    cPZ.construct ⊆ (cPZ.ellipsoid σ).construct :=
  subset_trans cPZ.polyZonotope_contains (cPZ.polyZonotope.ellipsoid_contains σ hσ hh)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
