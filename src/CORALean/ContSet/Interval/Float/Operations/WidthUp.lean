import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.widthUp` over floats

The width of one coordinate, rounded up and clipped at `zero`: a crossed coordinate counts as `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.widthUp (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  maximum zero (subUp (I.sup i) (I.inf i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
