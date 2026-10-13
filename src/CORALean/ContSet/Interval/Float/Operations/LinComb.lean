import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.linComb`

The box around both, as over ℝ. Exact: `minimum` and `maximum` pick one of the
two stored floats and invent no digits, so neither bound rounds.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.linComb (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => minimum (I₁.inf i) (I₂.inf i)
  sup := fun i => maximum (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
