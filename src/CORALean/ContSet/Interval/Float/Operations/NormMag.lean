module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.normMag` over floats

The entrywise larger of `|inf|` and `|sup|`, which `absolute` and `maximum` give exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.normMag (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => maximum (absolute (I.inf i)) (absolute (I.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
