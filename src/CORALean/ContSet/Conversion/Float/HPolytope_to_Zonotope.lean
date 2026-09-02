import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# A halfspace description as a zonotope, over a floating-point scalar

Through its box, which is what the certificates give.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 n}

def HPolytope.zonotope (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : Zonotope 𝕋 n :=
  (HPolytope.interval up lo).zonotope

theorem HPolytope.subset_zonotope (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.zonotope up lo).construct :=
  subset_trans (HPolytope.interval_outer up lo) (Interval.subset_zonotope _)


end CORALean.Float
