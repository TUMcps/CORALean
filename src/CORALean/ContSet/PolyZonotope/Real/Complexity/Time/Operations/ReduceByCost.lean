module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.reduceByCost`

Asserted, not proved: `Operations/ReduceBy.lean` copies the kept columns of
both blocks and their exponents, which is free here, and builds the diagonal
block from `dropRadius` — one row sum per output coordinate over the `r`
absorbed dependent and `rI` absorbed independent generators, `n * (r + rI)`
absolute values and one addition fewer.

The `n * (n - 1)` off-diagonal zeros are written, not computed, so neither the
kept counts nor the block's own width enter.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduceBy` costs at `Vec ℝ n` absorbing `r` dependent and
`rI` independent generators: `2 * n * (r + rI)`, and nothing for what is kept. -/
def PolyZonotope.reduceByCost (n r rI : ℕ) : Cost := ⟨2 * (n * (r + rI))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
