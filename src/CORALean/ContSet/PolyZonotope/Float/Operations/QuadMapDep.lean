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

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- The map on a set with no independent block and no error box. Sound only
there, so nothing calls it directly. -/
def PolyZonotope.quadMapDep (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    PolyZonotope 𝕋 m where
  p := S.p
  h := (S.h + 1) * (S.h + 1)
  q := 0
  c := fun _ => zero
  G := PolyZonotope.quadMapGDown Q S
  E := PolyZonotope.quadMapE S
  GI := fun _ => Fin.elim0
  err := PolyZonotope.generatorError (PolyZonotope.quadMapGDiff Q S)

end CORALean.Float
