import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# The stored half-difference of two centres

Split out of `LinComb.lean` (issue #62): read again by
`Theorems/LinCombOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stored half-difference of the two centres: the generator the fresh
factor slides along. -/
def PolyZonotope.halfDiff (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (subDown (a i) (b i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
