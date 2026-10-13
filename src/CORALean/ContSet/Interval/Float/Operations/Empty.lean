import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.empty`

The crossed box, lower bound `one` and upper bound `zero` in every coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
