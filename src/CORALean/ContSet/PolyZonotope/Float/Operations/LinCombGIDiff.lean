import CORALean.ContSet.PolyZonotope.Float.Operations.LinCombGI

/-!
# What `linComb`'s stored independent generators fall short by

Split out of `LinComb.lean` (issue #62): read again by
`Theorems/LinCombOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- What the stored independent generators fall short by: the gap between the
two directed roundings, which a coefficient in `[-1,1]` then spreads either
way. -/
def PolyZonotope.linCombGIDiff (PZ₁ PZ₂ : PolyZonotope 𝕋 n) : Mat 𝕋 n (PZ₁.q + PZ₂.q) :=
  fun i j => subUp (PolyZonotope.linCombGI addUp subUp PZ₁ PZ₂ i j)
    (PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂ i j)

end CORALean.Float
