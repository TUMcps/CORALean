import CORALean.ContSet.Interval.Float.Interval

/-!
# `Zonotope.errBound`

The largest magnitude in each entry of a float box: the larger of the two ends' absolute values.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.errBound (E : Interval (Vec 𝕋 n)) : Vec 𝕋 n := fun i =>
  maximum (absolute (E.inf i)) (absolute (E.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
