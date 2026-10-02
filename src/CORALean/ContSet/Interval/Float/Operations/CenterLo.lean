import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.centerLo` over floats

The midpoint with the sum rounded down: at most the real midpoint.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.centerLo (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => half (addDown (I.inf i) (I.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
