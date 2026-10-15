module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.reduceByCost`

Asserted, not proved: `Operations/ReduceBy.lean` copies the `q` kept
generators, which is free here, and builds the diagonal block from one row sum
per output coordinate — `n * r` absolute values and `n * (r - 1)` additions
over the `r` absorbed generators. The `n * (n - 1)` off-diagonal zeros are
written, not computed, so `q` and the block's own width do not enter.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceBy` costs at `Vec ℝ n` absorbing `r` generators:
`2 * n * r`, and nothing for the kept block. -/
def Zonotope.reduceByCost (n r : ℕ) : Cost := ⟨2 * (n * r)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
