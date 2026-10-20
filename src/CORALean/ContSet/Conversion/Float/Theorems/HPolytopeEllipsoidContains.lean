module

public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A halfspace description as an ellipsoid, over a floating-point scalar

Through its zonotope, which is its box, from the same certificates.

## Inputs
* `P` – halfspace polytope
* `σ` – scaling factor

## Hypotheses
* `up` – float upper bound per coordinate
* `lo` – float lower bound per coordinate
* `hσ` – scaling factor positive
* `hh` – squared scaling factor at least generator count

## Conclusion
* polytope is contained in its ellipsoid
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

theorem HPolytope.ellipsoid_contains {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : ((HPolytope.zonotope up lo).h : ℝ) ≤ toReal (mulDown σ σ)) :
    P.construct ⊆ (HPolytope.ellipsoid up lo σ).construct :=
  subset_trans (HPolytope.zonotope_contains up lo)
    ((HPolytope.zonotope up lo).ellipsoid_contains σ hσ hh)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
