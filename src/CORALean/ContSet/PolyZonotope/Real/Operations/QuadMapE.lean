import CORALean.ContSet.PolyZonotope.Real.Operations.BilinE

/-!
# The exponent matrix of `quadMap`

`bilinE` at one set paired with itself: a quadratic map is a pairing over shared
factors, and its exponent arithmetic never reads the ambient type, so there is
nothing here beyond the name. `Fin.cast rfl` is the identity, which is why the
two factor indices need no reconciling.

Its own file (issue #62): read again by the float layer's own `quadMap`, by
`Theorems/QuadMapOuter.lean`, `Theorems/QuadMapENominal.lean`,
`Theorems/QuadEvalSumExt.lean`, and by `ConPolyZono.quadMapDep`, all outside
this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added: the factors are shared, so the
product of two monomials is a monomial again. -/
def PolyZonotope.quadMapE (S : PolyZonotope α) :
    Fin S.p → Fin ((S.h + 1) * (S.h + 1)) → ℕ :=
  PolyZonotope.bilinE S S rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
