import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGUp

/-!
# `quadMap`'s generators, rounded up

Split out of `QuadMap.lean` (issue #62): read again by `quadMapGDiff` in this
directory and by `Theorems/QuadMapOuter.lean`, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.quadMapGUp (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 m ((pZ.h + 1) * (pZ.h + 1)) :=
  PolyZonotope.bilinGUp Q pZ pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
