import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.enclosePoints`

The coordinatewise minimum and maximum of a family of `k` points. Exact: `minimum` and `maximum`
round nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.enclosePoints {k : ℕ} (p : Fin k → Vec 𝕋 n) : Interval (Vec 𝕋 n) where
  inf := fun i => minimumOver fun l => p l i
  sup := fun i => maximumOver fun l => p l i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
