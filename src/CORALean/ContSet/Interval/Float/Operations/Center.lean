import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.center` over floats

CORA's `center`, the midpoint of the two bounds. `half` is exact, so the one rounding is the sum,
and `center` rounds it up: the stored centre is at least the real midpoint (`Theorems/CenterGe`).
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

/-- Any point of the box would do for a zonotope's centre; the midpoint keeps the generators small.
The sum rounds up, so this is at least the real midpoint. -/
def Interval.center (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n := fun i => half (addUp (I.inf i) (I.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
