import CORALean.ContSet.Zonotope.Float.Operations.LinCombG

/-!
# The gap `linComb`'s generators fall short by

Split out of `LinComb.lean` (issue #62): `Theorems/LinCombOuter.lean` reads
this directly, outside this file.

The gap between the two directed roundings of the same generator matrix, which
a coefficient in `[-1,1]` then spreads either way — what `generatorError`
below turns into a box.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the stored generators fall short by: the gap between the two directed
roundings, which a coefficient in `[-1,1]` then spreads either way. -/
def Zonotope.linCombGDiff (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : Mat 𝕋 n (Z₁.h + Z₂.h + 1) :=
  fun i j => subUp (Zonotope.linCombG addUp subUp Z₁ Z₂ i j)
    (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
