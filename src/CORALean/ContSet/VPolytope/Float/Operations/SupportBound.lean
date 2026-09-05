import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundDot
import CORALean.ContSet.Interval.Float.Operations.BoundDot

/-!
# A float vertex description answers a general direction

At the price the coordinate directions avoid: a rounded dot product per
vertex, then the largest of them, plus the error box's own reach, added
upward.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.boundDot (P : VPolytope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 P.construct c :=
  InflatedContSet.boundOfParts (P.nominalBoundDot a hc) (P.E.boundDot a hc)

end CORALean.Float
