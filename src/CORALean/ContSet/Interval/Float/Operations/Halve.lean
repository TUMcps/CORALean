import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.halve`, a box scaled by one half
Both bounds halved, which is exact in a binary format (`half` only moves the exponent), so no
outward rounding is needed.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.halve (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => half (I.inf i)
  sup := fun i => half (I.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
