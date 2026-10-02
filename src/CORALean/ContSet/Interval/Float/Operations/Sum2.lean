import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.sum₂` over floats

CORA's `sum` of an interval matrix along each row: the lower bounds are summed rounding down and
the upper bounds rounding up, so the stored box holds every column sum the exact one does.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.sum₂ (I : Interval (Mat 𝕋 m n)) : Interval (Vec 𝕋 m) where
  inf := fun i => sumDown fun j => I.inf i j
  sup := fun i => sumUp fun j => I.sup i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
