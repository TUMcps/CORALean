import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.abs`

`max 0 (inf, -sup)` and `max (-inf, sup)`; `neg` and `maximum` are exact, so nothing rounds.
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

def Interval.abs (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => maximum zero (maximum (I.inf i) (neg (I.sup i)))
  sup := fun i => maximum (neg (I.inf i)) (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
