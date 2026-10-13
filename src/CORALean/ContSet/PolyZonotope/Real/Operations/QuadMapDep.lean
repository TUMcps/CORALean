import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

/-!
# `quadMap` at a set whose coefficients are all dependent

`bilin` at `quadBilin`, one set paired with itself: every field is the one the
shared pairing already builds, `quadMapG` and `quadMapE` being that pairing's
generators and exponent columns.

Its own file (issue #62): read again by the float layer's own `quadMap` and
`Theorems/QuadMapOuter.lean`, both outside this file. Sound only where the
independent block is empty, so nothing outside `quadMap` calls it directly.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. -/
def PolyZonotope.quadMapDep (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) :=
  PolyZonotope.bilin (PolyZonotope.quadBilin Q) pZ pZ rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
