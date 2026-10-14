module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.generatorError`

What generators known only to within `G` entrywise cost. Both generator blocks
pay into this one box: the independent block because its coefficients range over
`[-1,1]`, the dependent block because its monomials do too. A row therefore sums
with no cancellation either way, which is `radius`.

Not `Zonotope.generatorError`, which is the same expression: the two
representations stay independent of each other, and what they share is
`abs_sum_le_radius` in `Global`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.generatorError (G : Mat 𝕋 n h) : Interval (Vec 𝕋 n) :=
  Interval.symmetric (radius G)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
