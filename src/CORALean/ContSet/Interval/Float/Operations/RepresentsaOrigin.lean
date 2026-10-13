module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.representsa_origin`

The origin test at float: each bound is `≤ 0` and `≥ 0`. One direction only, as `le`.
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

def Interval.representsa_origin (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j =>
    FloatOps.le (I.inf j) zero && FloatOps.le zero (I.inf j) &&
    FloatOps.le (I.sup j) zero && FloatOps.le zero (I.sup j)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
