import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

/-!
# A constrained zonotope as a box, over a floating-point scalar

Constraints dropped, then the zonotope's own box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ConZonotope.interval (C : ConZonotope 𝕋 n) : Interval 𝕋 n :=
  C.zonotope.interval

theorem ConZonotope.interval_outer (C : ConZonotope 𝕋 n) :
    C.construct ⊆ C.interval.construct :=
  subset_trans C.zonotope_outer (Zonotope.interval_outer _)


end CORALean.Float
