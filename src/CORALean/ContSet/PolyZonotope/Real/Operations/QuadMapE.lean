module

public import CORALean.ContSet.PolyZonotope.Real.Operations.BilinE

@[expose] public section

/-!
# The exponent matrix of `quadMap`

`bilinE` at one set paired with itself: a quadratic map is a pairing over shared factors, and
its exponent arithmetic never reads the ambient type, so there is nothing here beyond the
name. `Fin.cast rfl` is the identity, so the two factor indices need no reconciling. Its own
file (issue #62): read again by the float layer's `quadMap`, `Theorems/QuadMapOuter.lean`,
`Theorems/QuadMapENominal.lean`, `Theorems/QuadEvalSumExt.lean` and `ConPolyZono.quadMapDep`.

## Inputs
* `pZ` – polynomial zonotope

## Output
* exponent matrix of the quadratic image
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added: the factors are shared, so the
product of two monomials is a monomial again. -/
def PolyZonotope.quadMapE (pZ : PolyZonotope α) :
    Fin pZ.p → Fin ((pZ.h + 1) * (pZ.h + 1)) → ℕ :=
  PolyZonotope.bilinE pZ pZ rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
