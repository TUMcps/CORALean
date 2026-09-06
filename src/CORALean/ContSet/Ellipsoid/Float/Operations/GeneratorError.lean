import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
import CORALean.ContSet.Interval.Float.Operations.Symmetric

/-!
# `Ellipsoid.generatorError`

What generators known only to within `G` entrywise cost. A row is summed with no
cancellation, which is `radius`, and the box is symmetric because `u` reaches
every sign.

Not `Zonotope.generatorError`, which is the same expression: the two
representations stay independent of each other, and what they share is
`abs_sum_le_radius` in `Global`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.generatorError (G : Mat 𝕋 n k) : Interval 𝕋 n := Interval.symmetric (radius G)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
