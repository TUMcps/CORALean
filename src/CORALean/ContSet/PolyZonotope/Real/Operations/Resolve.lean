module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset

@[expose] public section

/-!
# `PolyZonotope.resolve`

CORA's `@polyZonotope/resolve.m` for one factor: substitute the value `x` for the factor `id`,
`G .* prod(x.^eMx, 1)`, and fold the columns that no longer depend on any factor into the
center. Here it is `getSubset` at the degenerate interval `[x, x]` (center `x`, radius `0`),
which substitutes the value into every monomial and keeps the factor as a column of the
exponent matrix. Identity is positional, so a resolved factor is not removed from the list as
CORA removes its `id`, and `compact` is the operation that folds and drops what is constant. A
list of factors is the iteration.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index
* `x` – value of the factor

## Output
* polynomial zonotope with that factor fixed
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Factor `k` fixed at the value `x`. -/
def PolyZonotope.resolve (pZ : PolyZonotope α) (k : Fin pZ.p) (x : ℝ) : PolyZonotope α :=
  pZ.getSubset k x 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
