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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The image's exponent column, the two columns added. Over ℕ, so exact. -/
def PolyZonotope.quadMapE (pZ : PolyZonotope 𝕋 n) :
    Fin pZ.p → Fin ((pZ.h + 1) * (pZ.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE pZ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE pZ k (finProdFinEquiv.symm l).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
