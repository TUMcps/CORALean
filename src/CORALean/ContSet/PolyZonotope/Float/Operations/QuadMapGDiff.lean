import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapGUp

/-!
# How far a stored `quadMap` generator can be from the exact bilinear form

Split out of `QuadMap.lean` (issue #62): read again by `quadMapDep` in this
directory and by `Theorems/QuadMapOuter.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- How far a stored generator can be from the exact bilinear form. -/
def PolyZonotope.quadMapGDiff (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    Mat 𝕋 m ((S.h + 1) * (S.h + 1)) :=
  fun k l => subUp (PolyZonotope.quadMapGUp Q S k l) (PolyZonotope.quadMapGDown Q S k l)

end CORALean.Float
