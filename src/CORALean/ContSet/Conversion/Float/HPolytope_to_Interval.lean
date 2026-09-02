import CORALean.ContSet.HPolytope.Float.Operations.DualBound
import CORALean.ContSet.Interval.Float.Operations.OfBounds

/-!
# A halfspace description as a box, over a floating-point scalar

`2n` certified bounds read into a box. Nothing rounds here — each bound was
already rounded outward where it was computed, and negating a float is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 n}

def HPolytope.interval (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : Interval 𝕋 n :=
  Interval.ofBounds up lo

theorem HPolytope.interval_outer
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.interval up lo).construct :=
  Interval.subset_ofBounds up lo

end CORALean.Float
