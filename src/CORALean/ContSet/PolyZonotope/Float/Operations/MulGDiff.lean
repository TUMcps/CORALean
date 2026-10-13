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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far a stored generator can be from the exact product. -/
def PolyZonotope.mulGDiff (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 n ((pZ₁.h + 1) * (pZ₂.h + 1)) :=
  fun i l => subUp (PolyZonotope.mulGUp pZ₁ pZ₂ i l) (PolyZonotope.mulGDown pZ₁ pZ₂ i l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
