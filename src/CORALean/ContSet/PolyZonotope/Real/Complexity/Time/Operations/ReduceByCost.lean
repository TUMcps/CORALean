module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.reduceByCost`

Asserted, not proved: `Operations/ReduceBy.lean` copies the kept columns of both blocks and
their exponents, which costs their writes, and builds the diagonal block from `dropRadius`:
one row sum per output coordinate over the `r` absorbed dependent and `rI` absorbed independent
generators, `n * (r + rI)` absolute values and one addition fewer. The `n * (n - 1)` off-diagonal
zeros are written, not computed. Every scalar of the result is also a write: the center, `d`
kept dependent generators with exponents, `dI` kept independent ones and the `n` by `n` block.

## Inputs
* `n` – dimension
* `p` – number of factors
* `d` – kept dependent generators
* `dI` – kept independent generators
* `r` – dropped dependent generators
* `rI` – dropped independent generators

## Output
* operation count of the reduction by a split
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduceBy` costs at `Vec ℝ n` over `p` factors, keeping `d` dependent and
`dI` independent generators and absorbing `r` dependent and `rI` independent ones:
`2 * n * (r + rI)` for the row sums, and `n * (1 + d + dI + n) + p * d` writes for the result. -/
def PolyZonotope.reduceByCost (n p d dI r rI : ℕ) : Cost :=
  ⟨2 * (n * (r + rI)) + (n * (1 + d + dI + n) + p * d)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
