import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.MulGUp

/-!
# How far a stored `mul` generator can be from the exact product

Split out of `Mul.lean` (issue #62): read again by `Theorems/EvalPolyOuter.lean`,
`Theorems/MulGClose.lean` and `Theorems/MulOuter.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- How far a stored generator can be from the exact product. -/
def PolyZonotope.mulGDiff (S₁ S₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n ((S₁.h + 1) * (S₂.h + 1)) :=
  fun i l => subUp (PolyZonotope.mulGUp S₁ S₂ i l) (PolyZonotope.mulGDown S₁ S₂ i l)

end CORALean.Float
