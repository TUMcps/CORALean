module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` at `Q : Fin m → Mat ℝ n n` and
`h` generators evaluates, per output coordinate, a bilinear form `xᵀ Q y`
(`Cost.matVec n n` plus a dot product, `2 * n * n + 2 * n`) for the center term
(`h + 1` of them), twice for each of the `h` linear terms, once for each of the
`h` squared terms and twice for each of the `h * h` index pairs, with `O(1)`
additions or scalings around each. Summed, that is at most
`m * (h + 1)^2 * (4 * n * n + 4 * n + 2)`; the count is the plain polynomial,
the squared-terms and pair-terms share counted at the pair rate.

Under `Global/Cost.lean`'s model every scalar of the result is also a write, one unit each, and the
result's center and `(h + 1)^2 - 1` generators of
`m` entries are `m * (h + 1)^2` of them.
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
