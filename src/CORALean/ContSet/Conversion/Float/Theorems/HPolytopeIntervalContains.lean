module

public import CORALean.ContSet.HPolytope.Float.Operations.DualBound
public import CORALean.ContSet.Interval.Float.Operations.OfBounds
public import CORALean.ContSet.Interval.Float.Theorems.SubsetOfBounds
public import CORALean.ContSet.Conversion.Float.Operations.Basic

@[expose] public section

/-!
# A halfspace description as a box, over a floating-point scalar

`2n` certified bounds read into a box. Nothing rounds here — each bound was
already rounded outward where it was computed, and negating a float is exact.

## Inputs
* none

## Hypotheses
* `up` – float upper bound per coordinate
* `lo` – float lower bound per coordinate

## Conclusion
* polytope is contained in its interval
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.interval_contains
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.interval up lo).construct :=
  Interval.subset_ofBounds up lo

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
