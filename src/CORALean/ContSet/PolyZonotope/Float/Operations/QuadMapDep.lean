import CORALean.ContSet.PolyZonotope.Float.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapE
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapGDown

/-!
# `quadMap` at a set with no independent block and no error box

Split out of `QuadMap.lean` (issue #62): read again by
`Theorems/QuadMapOuter.lean`, outside this file. Sound only where the
independent block and the error box are both empty, so nothing outside
`quadMap` calls it directly.
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

/-- The map on a set with no independent block and no error box. Sound only
there, so nothing calls it directly. -/
def PolyZonotope.quadMapDep (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 m) := PolyZonotope.bilin Q pZ pZ rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
