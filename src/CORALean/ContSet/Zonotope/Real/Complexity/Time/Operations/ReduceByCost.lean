module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.reduceByCost`

Asserted, not proved: `Operations/ReduceBy.lean` copies the `q` kept generators and the center,
and builds the diagonal block from one row sum per output coordinate — `n * r` absolute values
and `n * (r - 1)` additions over the `r` absorbed generators. The result is the center, the `q`
kept generators and the `n` by `n` diagonal block, `n * (1 + q + n)` scalars, each a write, the
block's zeros included.

## Inputs
* `n` – dimension
* `q` – kept generator count
* `r` – absorbed generator count

## Output
* row sums `2nr` plus `n(1+q+n)` writes
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceBy` costs at `Vec ℝ n` keeping `q` and absorbing `r` generators:
`2 * n * r` for the row sums, and `n * (1 + q + n)` writes for the result. -/
def Zonotope.reduceByCost (n q r : ℕ) : Cost := ⟨2 * (n * r) + n * (1 + q + n)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
