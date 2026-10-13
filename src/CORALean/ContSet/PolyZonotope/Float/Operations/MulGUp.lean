import CORALean.ContSet.PolyZonotope.Float.Operations.ExtG

/-!
# `mul`'s generators, rounded up

Split out of `Mul.lean` (issue #62): read again by `Theorems/MulGClose.lean`,
outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.mulGUp (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 n ((pZ₁.h + 1) * (pZ₂.h + 1)) :=
  fun i l => mulUp (PolyZonotope.extG pZ₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG pZ₂ i (finProdFinEquiv.symm l).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
