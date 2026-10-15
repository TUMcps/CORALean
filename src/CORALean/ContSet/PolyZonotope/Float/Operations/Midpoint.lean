module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# The stored midpoint of two centers

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

/-- The stored midpoint of the two centers. -/
def PolyZonotope.midpoint (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (addDown (a i) (b i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
