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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.zonotope (P : VPolytope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  P.interval.zonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.zonotope_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.zonotope.construct :=
  subset_trans P.interval_contains (Interval.zonotope_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
