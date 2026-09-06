import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

/-!
# `PolyZonotope.quadMap`

CORA's `@polyZonotope/quadMap`, and the operation the representation exists for:
the image under `x ↦ (xᵀQ₁x, …, xᵀQₘx)` of a polynomial zonotope is a polynomial
zonotope, exactly. A zonotope has no such closure — the image of a zonotope
under a quadratic map is generally not a zonotope — and the reason this one does
is that the factors are shared: `mᵢ mⱼ` is again a monomial, in the exponent
column `Eᵢ + Eⱼ`.

`extG`/`extE` fold the centre in as generator zero with the all-zero exponent
column, so a point is one sum rather than a centre plus a sum; `quadMapG`/
`quadMapE` are then a plain double sum, indexed by pairs through
`finProdFinEquiv` since the structure carries a count and not an index type.

Independent generators are handled before the map: `quadMap` runs `quadMapDep`
on `dependent`, whose independent block is empty by construction, which keeps
the operation total and exact at once.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.quadMap (Q : Fin m → Mat ℝ n n) (PZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) := PolyZonotope.quadMapDep Q PZ.dependent

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
