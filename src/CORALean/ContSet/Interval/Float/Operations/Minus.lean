module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.minus`

Each bound rounds away from the interval: `inf` down, `sup` up.
-/

-- Authors:       Claude Opus 5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.minus (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => subDown (I₁.inf i) (I₂.sup i)
  sup := fun i => subUp (I₁.sup i) (I₂.inf i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
