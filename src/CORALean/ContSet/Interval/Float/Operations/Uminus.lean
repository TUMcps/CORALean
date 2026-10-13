module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.uminus`

Negation is exact, `neg` flipping a sign bit, so the bounds swap and negate with no rounding.
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

def Interval.uminus (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => neg (I.sup i)
  sup := fun i => neg (I.inf i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
