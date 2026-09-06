import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# A masked fibre sum, rounded down

Split out of `Compact.lean` (issue #62): read again by `mergedCol` in this
directory and by `Theorems/FiberDownLe.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}

/-- A fibre summed downward, masked rather than restricted: the columns outside
it contribute `zero`, which is what lets `sumDown` over `Fin h` answer a sum
over a `Finset`. -/
def PolyZonotope.fiberDown (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n) (j : Fin h) : 𝕋 :=
  sumDown fun l => if r l = j then G i l else zero

end CORALean.Float
