module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` at `Q : Fin m → Mat ℝ n n` and `h` generators
evaluates, per output coordinate, a bilinear form `xᵀ Q y` (`2 * n * n + 2 * n`) for the center
term, twice for each of the `h` linear terms, once for each of the `h` squared terms and twice for
each of the `h * h` index pairs, with `O(1)` operations around each: at most
`m * (h + 1)^2 * (4 * n * n + 4 * n + 2)`, the squared and pair terms counted at the pair rate.
The result's `m * (h + 1)^2` entries are also writes.

## Inputs
* `m` – output dimension
* `n` – input dimension
* `h` – generator count

## Output
* cost of the arithmetic and `m(h+1)²` writes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.quadMap` costs at `Q : Fin m → Mat ℝ n n` and `h` generators: the
arithmetic and `m * (h + 1) ^ 2` writes, one for each entry of the result's center and generator
matrix. -/
def Zonotope.quadMapCost (m n h : ℕ) : Cost :=
  ⟨m * ((h + 1) ^ 2 * (4 * (n * n) + 4 * n + 3))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
