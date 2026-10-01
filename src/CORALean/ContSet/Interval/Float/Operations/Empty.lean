import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.empty`

The crossed box, lower bound `one` and upper bound `zero` in every coordinate.
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

def Interval.empty (n : ℕ) : Interval (Vec 𝕋 n) where
  inf := fun _ => one
  sup := fun _ => zero


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
