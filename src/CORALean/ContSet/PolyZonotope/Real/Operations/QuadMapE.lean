import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE

/-!
# The exponent matrix of `quadMap`

Split out of `QuadMap.lean` (issue #62): read again by the float layer's own
`quadMap`, by `Theorems/QuadMapOuter.lean`, `Theorems/QuadMapENominal.lean`,
`Theorems/QuadEvalSumExt.lean`, and by `ConPolyZono.quadMapDep`, all outside
this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added: the factors are shared, so the
product of two monomials is a monomial again. -/
def PolyZonotope.quadMapE (S : PolyZonotope α) :
    Fin S.p → Fin ((S.h + 1) * (S.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S k (finProdFinEquiv.symm l).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
