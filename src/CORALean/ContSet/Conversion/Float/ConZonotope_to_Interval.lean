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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ConZonotope.interval (cZ : ConZonotope 𝕋 n) : Interval (Vec 𝕋 n) :=
  cZ.zonotope.interval


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.interval_contains (cZ : ConZonotope 𝕋 n) :
    cZ.construct ⊆ cZ.interval.construct :=
  subset_trans cZ.zonotope_contains (Zonotope.interval_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
