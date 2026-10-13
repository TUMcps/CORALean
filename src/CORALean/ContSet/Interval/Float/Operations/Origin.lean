module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.origin`

The point interval at the origin of `𝕋ⁿ`, every bound `zero`.
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

def Interval.origin (n : ℕ) : Interval (Vec 𝕋 n) where
  inf := fun _ => zero
  sup := fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
