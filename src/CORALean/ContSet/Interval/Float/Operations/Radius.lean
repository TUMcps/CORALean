import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.radius` over floats

CORA's `rad`, half the width. `half` is exact, so the one rounding is the difference, and it
rounds up: the stored radius is at least the real one.
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

def Interval.radius (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n := fun i => half (subUp (I.sup i) (I.inf i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
