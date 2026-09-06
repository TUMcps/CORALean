import CORALean.ContSet.Interval.Float.Interval

/-!
# What one generator per coordinate must reach to cover a box

Split out of `Dependent.lean` (issue #62): read again by `evalPoly`, by
`Conversion/PolyZonotope_to_Interval.lean`, and by several `Theorems/` files,
all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- What one generator per coordinate must reach to cover the box, exactly. -/
def PolyZonotope.errorBound (I : Interval 𝕋 n) : Vec 𝕋 n :=
  fun i => maximum (absolute (I.inf i)) (absolute (I.sup i))

end CORALean.Float
