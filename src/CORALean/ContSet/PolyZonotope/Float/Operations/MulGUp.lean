import CORALean.ContSet.PolyZonotope.Float.Operations.ExtG

/-!
# `mul`'s generators, rounded up

Split out of `Mul.lean` (issue #62): read again by `Theorems/MulGClose.lean`,
outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def PolyZonotope.mulGUp (S₁ S₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n ((S₁.h + 1) * (S₂.h + 1)) :=
  fun i l => mulUp (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)

end CORALean.Float
