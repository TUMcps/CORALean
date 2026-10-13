module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.representsa_point`

The point test at float: both bounds compare `≤` each other in every coordinate. One direction
only, as `le`.
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

def Interval.representsa_point (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => FloatOps.le (I.sup j) (I.inf j) && FloatOps.le (I.inf j) (I.sup j)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
