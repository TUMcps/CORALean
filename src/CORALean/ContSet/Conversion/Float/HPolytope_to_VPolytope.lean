import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval
import CORALean.ContSet.HPolytope.Float.Theorems.CertifiedOuter

/-!
# Halfspaces to vertices, over a floating-point scalar

Through a box, as in the exact layer: `2n` certified bounds, then `2ⁿ` corners.
The rounding has all been paid by the time the bounds arrive, and copying them
into corners costs nothing more.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 n}

def HPolytope.vPolytopeBox (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : VPolytope 𝕋 n :=
  Interval.vPolytope (HPolytope.interval up lo)

theorem HPolytope.subset_vPolytopeBox (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.vPolytopeBox up lo).construct :=
  subset_trans (HPolytope.interval_outer up lo) (Interval.subset_vPolytope _)

end CORALean.Float
