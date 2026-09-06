import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# A masked fibre sum, rounded up

Split out of `Compact.lean` (issue #62): read again by `mergedColUp` in this
directory and by `Theorems/LeFiberUp.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}

def PolyZonotope.fiberUp (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n) (j : Fin h) : 𝕋 :=
  sumUp fun l => if r l = j then G i l else zero

end CORALean.Float
