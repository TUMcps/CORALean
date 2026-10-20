module

public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains

@[expose] public section

/-!
# A polynomial zonotope as an ellipsoid, over a floating-point scalar

Through the zonotope enclosure, then that zonotope's `√h` ball, whose `σ` is proposed by
the caller and checked as in `Zonotope.ellipsoid`; here `h` counts the dependent and the
independent generators together.

## Inputs
* `pZ` – polynomial zonotope
* `σ` – scaling factor

## Hypotheses
* `hσ` – scaling factor positive
* `hh` – squared scaling factor at least factor count

## Conclusion
* set is contained in its ellipsoid
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

theorem PolyZonotope.ellipsoid_contains (pZ : PolyZonotope (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : ((pZ.h + pZ.q : ℕ) : ℝ) ≤ toReal (mulDown σ σ)) :
    pZ.construct ⊆ (pZ.ellipsoid σ).construct :=
  subset_trans pZ.zonotope_contains (pZ.zonotope.ellipsoid_contains σ hσ hh)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
