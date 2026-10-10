import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.magnitudeMat`: how far an interval matrix reaches from the zero matrix

The larger of the two ends' absolute values, entry by entry: every matrix of the interval is
below it entrywise in absolute value (`abs_mulVec_le_magnitudeMat`).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reach of each entry from `0`. -/
def Interval.magnitudeMat (I : Interval (Mat 𝕋 m n)) : Mat 𝕋 m n :=
  fun i j => maximum (absolute (I.inf i j)) (absolute (I.sup i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
