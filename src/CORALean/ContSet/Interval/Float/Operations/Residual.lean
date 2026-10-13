import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.residual`

The box an operation owes when it stores a rounded vector: the intended value
lies in `[lo, hi]` but `stored` was written down, so `[lo - stored, hi - stored]`
covers the difference.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.residual (lo hi stored : Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  ⟨fun i => subDown (lo i) (stored i), fun i => subUp (hi i) (stored i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
