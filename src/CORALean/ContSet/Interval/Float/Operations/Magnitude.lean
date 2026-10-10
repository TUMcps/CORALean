import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.magnitude`: how far an interval vector reaches from the origin

The larger of the two ends' absolute values, per coordinate. A point of the interval is at most
this far from `0` in each coordinate (`abs_le_magnitude`), and it is the radius of the smallest
box about the origin that holds the interval.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reach of each coordinate from `0`. -/
def Interval.magnitude (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => maximum (absolute (I.inf i)) (absolute (I.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
