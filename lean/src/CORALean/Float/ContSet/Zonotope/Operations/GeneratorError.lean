import CORALean.Float.ContSet.Zonotope.Zonotope

/-!
# `Zonotope.generatorError`

What generators known only to within `G` entrywise cost: coefficients range over
`[-1, 1]`, so a row sums with no cancellation. The generator counterpart of
`Interval.residual`, and the box every operation that rounds `G` pays into.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}

def Zonotope.generatorError (G : Mat 𝕋 n h) : Interval 𝕋 n := Interval.symmetric (radius G)

end CORALean.Float
