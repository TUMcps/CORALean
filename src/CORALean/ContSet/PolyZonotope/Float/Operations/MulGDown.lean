import CORALean.ContSet.PolyZonotope.Float.Operations.ExtG

/-!
# `mul`'s generators, rounded down

Split out of `Mul.lean` (issue #62): read again by `Theorems/EvalPolyOuter.lean`,
`Theorems/MulGClose.lean` and `Theorems/MulOuter.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Generator `(i, j)` of the product, rounded down: one multiplication per
coordinate. -/
def PolyZonotope.mulGDown (S₁ S₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n ((S₁.h + 1) * (S₂.h + 1)) :=
  fun i l => mulDown (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
