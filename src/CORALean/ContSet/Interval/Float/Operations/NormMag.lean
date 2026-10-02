import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.normMag` over floats

The entrywise larger of `|inf|` and `|sup|`, which `absolute` and `maximum` give exactly.
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

def Interval.normMag (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => maximum (absolute (I.inf i)) (absolute (I.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
