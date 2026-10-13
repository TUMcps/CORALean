module

public import CORALean.ContSet.PolyZonotope.Float.Operations.LinCombGI

@[expose] public section

/-!
# What `linComb`'s stored independent generators fall short by

Split out of `LinComb.lean` (issue #62): read again by
`Theorems/LinCombOuter.lean`, outside this file.
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

/-- What the stored independent generators fall short by: the gap between the
two directed roundings, which a coefficient in `[-1,1]` then spreads either
way. -/
def PolyZonotope.linCombGIDiff (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) : Mat 𝕋 n (pZ₁.q + pZ₂.q) :=
  fun i j => subUp (PolyZonotope.linCombGI addUp subUp pZ₁ pZ₂ i j)
    (PolyZonotope.linCombGI addDown subDown pZ₁ pZ₂ i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
