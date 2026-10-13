module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# A masked fibre sum, rounded up

Split out of `Compact.lean` (issue #62): read again by `mergedColUp` in this
directory and by `Theorems/LeFiberUp.lean`, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.fiberUp (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n) (j : Fin h) : 𝕋 :=
  sumUp fun l => if r l = j then G i l else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
