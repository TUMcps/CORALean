import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# A hull as a zonotope, over a floating-point scalar

Through its box, the vertices' own error box having already been absorbed
there.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.zonotope (P : VPolytope 𝕋 n) : Zonotope 𝕋 n :=
  P.interval.zonotope

theorem VPolytope.subset_zonotope (P : VPolytope 𝕋 n) :
    P.construct ⊆ P.zonotope.construct :=
  subset_trans P.interval_outer (Interval.subset_zonotope _)


end CORALean.Float
