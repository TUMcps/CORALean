module

public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ConZonotope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the center and each of the
`h` generators through `M *ᵥ ·` and carries the constraint polytope over
unchanged, so it pays `h + 1` matrix-vector products and the writes of the polytope.

The same count as `Zonotope.mtimesCost` plus the polytope's writes, which stay: a linear map
needs no computation on the constraints, because they live over the coefficients and a linear
map does not move those.

## Inputs
* `m` – rows
* `n` – columns
* `h` – number of generators
* `r` – number of inequalities
* `re` – number of equalities

## Output
* the cost of multiplying by a matrix
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.mtimes` costs at `M : Mat ℝ m n` and `h` generators, a constraint polytope
of `r` inequality and `re` equality rows: one matrix-vector product for the center and one per
generator, and the writes of the polytope. -/
def ConZonotope.mtimesCost (m n h r re : ℕ) : Cost :=
  ConZonotope.mapCost (Cost.matVec m n) h r re

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
