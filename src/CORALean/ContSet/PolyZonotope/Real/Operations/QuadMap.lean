module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

@[expose] public section

/-!
# `PolyZonotope.quadMap`

CORA's `@polyZonotope/quadMap`, and the operation the representation exists for: the image
under `x ↦ (xᵀQ₁x, …, xᵀQₘx)` of a polynomial zonotope is a polynomial zonotope, exactly. A
zonotope has no such closure; this one does because the factors are shared: `mᵢ mⱼ` is a
monomial at the exponent column `Eᵢ + Eⱼ`. `extG`/`extE` fold the center in as generator zero,
and `quadMapG`/`quadMapE` are a plain double sum indexed by pairs through `finProdFinEquiv`.
Independent generators are handled before the map: `quadMap` runs `quadMapDep` on `dependent`,
whose independent block is empty, which keeps the operation total and exact at once.

## Inputs
* `Q` – family of quadratic form matrices
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope of the quadratic image
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.quadMap (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) := PolyZonotope.quadMapDep Q pZ.dependent

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
