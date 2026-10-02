import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.diag` over floats

A rearrangement: the diagonal matrix of a vector box has the float `zero` off the diagonal,
so nothing is rounded.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.diag (I : Interval (Vec 𝕋 n)) : Interval (Mat 𝕋 n n) where
  inf := fun i j => if i = j then I.inf i else zero
  sup := fun i j => if i = j then I.sup i else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
