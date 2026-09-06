import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG

/-!
# `quadMap` at a set whose coefficients are all dependent

Split out of `QuadMap.lean` (issue #62): read again by the float layer's own
`quadMap` and `Theorems/QuadMapOuter.lean`, both outside this file. Sound only
where the independent block is empty, so nothing outside `quadMap` calls it
directly.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

/-- The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. -/
def PolyZonotope.quadMapDep {n m : ℕ} (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) where
  p := S.p
  h := (S.h + 1) * (S.h + 1)
  q := 0
  c := 0
  G := PolyZonotope.quadMapG Q S
  E := PolyZonotope.quadMapE S
  GI := Fin.elim0

end CORALean.Real
