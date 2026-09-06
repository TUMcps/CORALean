import CORALean.ContSet.PolyZonotope.Float.Operations.ExtE

/-!
# The exponent matrix of `quadMap`, over a floating-point scalar

Split out of `QuadMap.lean` (issue #62): read again by
`Theorems/QuadMapOuter.lean` and `Theorems/QuadMapENominal.lean`, both outside
this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The image's exponent column, the two columns added. Over ℕ, so exact. -/
def PolyZonotope.quadMapE (S : PolyZonotope 𝕋 n) :
    Fin S.p → Fin ((S.h + 1) * (S.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S k (finProdFinEquiv.symm l).2

end CORALean.Float
