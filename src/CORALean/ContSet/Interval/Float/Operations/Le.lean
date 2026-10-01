import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.le`

The containment test at float, one `FloatOps.le` per bound. `le` is certified in one direction
only, so `true` is a proof and `false` is no refutation.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.le (I J : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => FloatOps.le (J.inf j) (I.inf j) && FloatOps.le (I.sup j) (J.sup j)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
