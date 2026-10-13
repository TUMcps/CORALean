import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.min`

The coordinatewise smaller of the bounds. `minimum` is exact, choosing between two floats, so
nothing is rounded.
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

def Interval.min (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => minimum (I₁.inf i) (I₂.inf i)
  sup := fun i => minimum (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
