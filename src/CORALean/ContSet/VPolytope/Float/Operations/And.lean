import CORALean.ContSet.VPolytope.Float.Operations.OfInterval
import CORALean.ContSet.VPolytope.Float.Operations.Interval
import CORALean.ContSet.Interval.Float.Operations.And

/-!
# `VPolytope.and`, over a floating-point scalar

Through boxes, as in the exact layer, and for the same reason: the
intersection's vertices are generally none of either operand's. Each operand's
box already absorbed its error box, intersecting boxes is exact, and the corners
are stored bounds copied — so this operation rounds nowhere, all of its
imprecision being in the detour rather than in the arithmetic.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.and (P₁ P₂ : VPolytope 𝕋 n) : VPolytope 𝕋 n :=
  VPolytope.ofInterval (P₁.interval.and P₂.interval)

end CORALean.Float
