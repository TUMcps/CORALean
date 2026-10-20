module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent

@[expose] public section

/-!
# `PolyZonotope.cubMap`

CORA's `@polyZonotope/cubMap`, `{ z = (xᵀ T x) * x | x ∈ pZ }` with `zᵢ = Σₖ xₖ (xᵀ T{i,k} x)`,
as `quadMap` is formalized: independent generators are made dependent first (`dependent`),
which keeps the operation total and exact at once. CORA keeps them independent and encloses
their cubic terms by a zonotope (`zonotope(pZindSum)`), so there its result is an enclosure
where this one is exact; for a set without independent generators the two agree.
`ind` (the non-zero tensor columns) is not modelled: a column left out is the zero matrix.

## Inputs
* `T` – family of cubic form tensors
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope of the cubic image
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.cubMap (T : Fin m → Fin n → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) := PolyZonotope.cubMapDep T pZ.dependent

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
