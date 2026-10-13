import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope

/-!
# A box as a constrained zonotope, over a floating-point scalar

Through the zonotope. The generators absorb the centre's rounding there, and the
constraint list stays empty here, so nothing further is paid.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Interval.conZonotope (I : Interval (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  I.zonotope.conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.conZonotope_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.conZonotope.construct :=
  subset_trans I.zonotope_contains (Zonotope.conZonotope_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
