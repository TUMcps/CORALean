import CORALean.ContSet.VPolytope.Float.Operations.OfInterval
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

def HPolytope.toVPolytopeBox (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : VPolytope 𝕋 n :=
  VPolytope.ofInterval (HPolytope.intervalOf up lo)

theorem HPolytope.subset_toVPolytopeBox (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.toVPolytopeBox up lo).construct :=
  subset_trans (HPolytope.intervalOf_outer up lo) (VPolytope.subset_ofInterval _)

end CORALean.Float
